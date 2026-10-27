// Copyright 2026, The Android Open Source Project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `gpt_gen` is a host tool for generating GPT (GUID Partition Table) disk images.
//!
//! It allows users to specify the disk size, partition table entries count, and
//! details of each partition (name, size, and optional file content).
//!
//! # Example Usage
//!
//! ```sh
//! ./bazel.sh run //bootable/libbootloader/gbl/tools/gpt_gen -- \
//!     --out disk.img --disk_size 1G \
//!     --partition="boot,32M,boot.img" \
//!     --partition="system,512M"
//! ```

use arrayvec::ArrayVec;
use clap::Parser;
use file_block_io::FileBlockIo;
use gbl_async::block_on;
use gbl_storage::{new_gpt_n, Disk, GptBuilder};
use std::fs::File;
use std::io::Read;

/// Command line arguments for `gpt_gen`.
#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Output file
    out: String,

    /// Disk size of the image. e.g. 1G, 512M, 1024K
    disk_size: String,

    /// Specifies a partition. Format should be --partition=<part name>,<size>,<file name>
    #[arg(long, action = clap::ArgAction::Append)]
    partition: Vec<String>,

    /// Number of entries in partition table. i.e. 128, 256
    #[arg(long = "entries_count", default_value_t = 128)]
    entries_count: u32,
}

/// Parses a size string with optional unit suffix (K, M) into bytes.
///
/// Supported suffixes:
/// - `k` or `K` for Kilobytes (1024 bytes)
/// - `m` or `M` for Megabytes (1024 * 1024 bytes)
/// - No suffix for bytes
fn parse_size_str(size_str: &str) -> Result<u64, String> {
    let size_str = size_str.to_lowercase();
    let (value_str, multiplier) = match size_str.chars().last() {
        Some('k') => (&size_str[..size_str.len() - 1], 1024),
        Some('m') => (&size_str[..size_str.len() - 1], 1024 * 1024),
        _ => (size_str.as_str(), 1),
    };
    let val = value_str.parse::<u64>().map_err(|e| e.to_string())?;
    Ok(val * multiplier)
}

fn main() {
    let args = Args::parse();

    let size = parse_size_str(&args.disk_size).unwrap();
    assert!(size % 512 == 0, "Disk size must be a multiple of 512");

    println!("Creating file {} of size {}", args.out, size);
    let io = FileBlockIo::new_create(&args.out, size)
        .inspect_err(|e| {
            eprintln!("Error creating file: {:?}", e);
        })
        .unwrap();

    let mut disk = Disk::<_, ArrayVec<Option<Vec<u8>>, 2>>::new_alloc_scratch(io)
        .inspect_err(|e| {
            eprintln!("Error creating Disk: {:?}", e);
        })
        .unwrap();

    // TODO(b/508260420): Support 256 entries if necessary.
    let mut gpt = new_gpt_n::<128>();
    let (mut builder, _) = GptBuilder::new(&mut disk, &mut gpt)
        .inspect_err(|e| {
            eprintln!("Error creating GptBuilder: {:?}", e);
        })
        .unwrap();

    let mut part_files = vec![];
    for (i, part_arg) in args.partition.iter().enumerate() {
        let part_arg: Vec<&str> = part_arg.split(',').collect();
        let name = part_arg.first().expect("Partition name is required");
        let size_str = part_arg.get(1).expect("Partition size is required");
        let part_size = parse_size_str(size_str).unwrap();

        println!("Adding partition: {} size: {}", name, part_size);
        builder.add(name, [0xaa; 16], [(i + 1) as u8; 16], 0, Some(part_size)).unwrap();
        let Some(file_str) = part_arg.get(2).filter(|v| !v.is_empty()) else {
            continue;
        };
        part_files.push((name.to_string(), file_str.to_string()));
    }

    // Write GPT partition tables to file.
    block_on(builder.persist()).unwrap();

    for (name, file_str) in part_files {
        println!("Writing file {} for partition {}", file_str, name);
        let mut file = File::open(file_str).unwrap();
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer).unwrap();
        block_on(disk.write_gpt_partition(&mut gpt, &name, 0, &mut buffer)).unwrap();
    }

    // We only do minimal initialization so that edk2 can recognize it.
    println!("Initializing Protective MBR...");
    let mut mbr = [0u8; 512];
    mbr[450] = 0xEE; // OS Type (GPT)
    mbr[454] = 0x01; // Starting LBA (1)
    mbr[458..462].copy_from_slice(&0xFFFFFFFFu32.to_le_bytes()); // Size in LBA (Max)
    mbr[510] = 0x55; // Signature
    mbr[511] = 0xAA;

    block_on(disk.write(0, &mut mbr)).unwrap();
    println!("Done.");
}
