import json
import os
import logging
import tempfile


# To generate rust-project.json from bazel, run
# bazel run @rules_rust//tools/rust_analyzer:gen_rust_project --norepository_disable_download @gbl//efi:main
# However, this yields incorrect source path.
# Your source file
# /usr/local/google/home/zhangkelvin/uefi-gbl-mainline/bootable/libbootloader/gbl/efi/src/main.rs
# would turn into
# /usr/local/google/home/uefi-gbl-mainline/out/bazel/output_user_root/e14d642d361d598c63507c64a56ecbc7/execroot/_main/external/gbl/efi/src/main.rs
# and this confuses the rust-analyzer. This script will resolve the right
# source path for you by checking if any of the parent path is a symlink,
# and resolve all symlinks to final destination.



def traverse(obj: dict):
  if isinstance(obj, dict):
    for (key, val) in obj.items():
      if key == "root_module" or key == "CARGO_MANIFEST_DIR":
        obj[key] = os.path.realpath(val)
        continue
      if key == "cfg" and isinstance(val, list):
        obj[key] = [o for o in val if o != "test"]
      traverse(val)
  elif isinstance(obj, list):
    for item in obj:
      traverse(item)


def main(argv):
  logging.basicConfig(level=logging.INFO)
  rust_project_json_path = "rust-project.json"
  if len(argv) == 2:
    rust_project_json_path = argv[1]
  rust_project_json_path = os.path.realpath(rust_project_json_path)
  project_root_path = os.path.dirname(rust_project_json_path)
  logging.info("Using %s as project root path", project_root_path)
  with open(rust_project_json_path, "r") as fp:
    data = json.load(fp)
    traverse(data)

  with tempfile.NamedTemporaryFile("w+") as fp:
    json.dump(data, fp.file, indent=True)
    os.rename(fp.name, rust_project_json_path)
    # create the tempfile again so deleting it works after exiting this scope
    with open(fp.name, "w"):
      pass


if __name__ == '__main__':
  import sys
  main(sys.argv)
