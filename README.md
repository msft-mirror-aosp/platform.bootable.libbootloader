## IDE Setup

For rust development, we recommend use VSCode + rust-analzyzer plugin.

rust-analyzer requires `rust-project.json` to work properly. Luckily, bazel has support for generating `rust-project.json` .
Simply run

```
bazel run @rules_rust//tools/rust_analyzer:gen_rust_project --norepository_disable_download @gbl//efi/...
```

`@gbl//efi/...` is the target to generate rust project for, here it means "everything under @gbl//efi/ directory" . Omitting the target specifier would result in analyzing "@/..." , which would mot likely fail due to some obscure reason. Should targets get moved around in the future, this path spec also need to be updated.

After generating `rust-project.json`, you would notice that your IDE still doesn't offer auto completion. This is because some source file paths pointing to bazel-output dir, and you are most likely editing source files in bootable/libbootloader. In addition, the generated rust-project.json sets "cfg=test" for all targets, which causes certain dependency graph to resolve incorrectly. To fix this, run

```
python3 bootable/libbootloader/rewrite_rust_project_path.py rust-project.json
```

And reload your IDE.