# Rust ZBI lib

Rust version of [C library](src/firmware/lib/zbi) to work with ZBI format.

See Rust documentation for `zbi` for library details.

# Notes

Currently [`sdk/lib/zbi-format`](sdk/lib/zbi-format) is not ready to provide Rust bindings from FIDL.
So we are using `buildgen` generated version from C headers: [`src/firmware/lib/zbi-rs/src/zbi_format.rs`](src/firmware/lib/zbi-rs/src/zbi_format.rs)

Another alternative is manually created version: [`src/sys/lib/fuchsia-zbi/abi`](src/sys/lib/fuchsia-zbi/abi).

# Dev flow

This is temporary approach until butter way is found (http://b/297795783).

Source of truth is considered Fuchsia version. To make any changes start with submitting it to Fuchsia tree, then copying to AOSP.

Current version is copied for following revision: [commit](https://cs.opensource.google/fuchsia/fuchsia/+/2c45d1be1e88b2f9c1e55c940a4385a7d32d8c1e)

To get just `zbi-rs` from Fuchsia following commands can be used:
```
git clone -n --depth=1 --filter=tree:0 sso://fuchsia/fuchsia
cd fuchsia/
git sparse-checkout set --no-clone src/firmware/lib/zbi-rs
git checkout 2c45d1be1e88b2f9c1e55c940a4385a7d32d8c1e
```

Changing Licence in source files is required at the moment.

AOSP also contains `zerocopy-0.6` which requires changes to Cargo.toml file.
