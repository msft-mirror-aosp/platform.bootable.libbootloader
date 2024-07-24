# Copyright (C) 2024 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Action that verifies all EFI protocols used by GBL are explicitly listed in README.md
"""

load("@rules_rust//rust/private:providers.bzl", "CrateInfo")

def _readme_test_rule_impl(ctx):
    shell_script = """
while [[ $# -gt 0 ]]; do
  case $1 in
    --in)
      INPUT=$2
      shift
      shift
      ;;
    --out)
      OUTPUT=$2
      shift
      shift
      ;;
    --readme)
      README=$2
      shift
      shift
      ;;
    *)
      echo "Unexpected argument: $1"
      exit 1
      ;;
  esac
done

if [ ! -f $README ]; then
  echo "README file doesn't exist: ${README}"
  exit 1
fi

ALL_INPUTS=$(echo ${INPUT} | sed 's/,/ /g')

DOCLESS_PROTOCOLS=""
PROTOCOLS=($(grep -hE 'impl ProtocolInfo for .* \\{' ${ALL_INPUTS} | awk '{print $4}' | sort))
for P in ${PROTOCOLS[@]}
do
  grep -Lq $P ${README} || DOCLESS_PROTOCOLS+="\n\t$P"
done

if [ ! -z "${DOCLESS_PROTOCOLS}" ]; then
  echo -e "Missing documentation for protocol(s):$DOCLESS_PROTOCOLS"
  exit 1
fi

UNUSED_PROTOCOLS=""
README_PROTOCOLS=($(grep -P " ?.*?Protocol$" ${README} | awk '{print $NF}' | sort | uniq))
for P in ${README_PROTOCOLS[@]}
do
  grep -qhE "impl ProtocolInfo for $P" ${ALL_INPUTS} || UNUSED_PROTOCOLS+="\n\t$P"
done

if [ ! -z "${UNUSED_PROTOCOLS}" ]; then
  echo -e "Unused protocol(s) found in documentation:$UNUSED_PROTOCOLS"
  exit 1
fi

touch $OUTPUT
"""

    out_file = ctx.actions.declare_file("%s.script" % ctx.attr.name)
    in_files = [s for d in ctx.attr.deps for s in d[CrateInfo].srcs.to_list()]
    readme = ctx.attr.readme
    args = ctx.actions.args()
    args.add_joined(
        "--in",
        in_files,
        join_with = ",",
    )
    args.add(
        "--out",
        out_file,
    )
    args.add(
        "--readme",
        readme[DefaultInfo].files.to_list()[0],
    )
    ctx.actions.run_shell(
        inputs = in_files + readme[DefaultInfo].files.to_list(),
        outputs = [out_file],
        arguments = [args],
        command = shell_script,
    )
    return [DefaultInfo(executable = out_file)]

readme_test = rule(
    implementation = _readme_test_rule_impl,
    attrs = {
        "deps": attr.label_list(
            providers = [CrateInfo],
        ),
        "readme": attr.label(
            allow_single_file = [".md"],
        ),
    },
    test = True,
)
