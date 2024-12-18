# Copyright (C) 2024 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import argparse
import os
import pathlib
import sys
from typing import Tuple, Optional

_BAZEL_REL_PATH = "prebuilts/kernel-build-tools/bazel/linux-x86_64/bazel"


def _partition(lst: list[str], index: Optional[int]) \
        -> Tuple[list[str], Optional[str], list[str]]:
    """Returns the triple split by index.

    That is, return a tuple:
    (everything before index, the element at index, everything after index)

    If index is None, return (the list, None, empty list)
    """
    if index is None:
        return lst[:], None, []
    return lst[:index], lst[index], lst[index + 1:]


class BazelWrapper(object):
    def __init__(self, workspace_dir: pathlib.Path, bazel_args: list[str]):
        """Splits arguments to the bazel binary based on the functionality.

        bazel [startup_options] command         [command_args] --               [target_patterns]
                                 ^- command_idx                ^- dash_dash_idx

        See https://bazel.build/reference/command-line-reference

        Args:
            workspace_dir: root of workspace.
            bazel_args: The list of arguments the user provides through command line
            env: existing environment
        """

        self.workspace_dir = workspace_dir

        self.bazel_path = self.workspace_dir / _BAZEL_REL_PATH

        command_idx = None
        for idx, arg in enumerate(bazel_args):
            if not arg.startswith("-"):
                command_idx = idx
                break

        self.startup_options, self.command, remaining_args = _partition(bazel_args,
                                                                        command_idx)

        # Split command_args into `command_args -- target_patterns`
        dash_dash_idx = None
        try:
            dash_dash_idx = remaining_args.index("--")
        except ValueError:
            # If -- is not found, put everything in command_args. These arguments
            # are not provided to the Bazel executable target.
            pass

        self.command_args, self.dash_dash, self.target_patterns = _partition(remaining_args,
                                                                             dash_dash_idx)

        self._parse_startup_options()
        self._parse_command_args()
        self._add_extra_startup_options()

    def add_startup_option_to_parser(self, parser):
        parser.add_argument(
            "-h", "--help", action="store_true",
            help="show this help message and exit"
        )

    def _parse_startup_options(self):
        """Parses the given list of startup_options.

        After calling this function, the following attributes are set:
        - absolute_user_root: A path holding bazel build output location
        - transformed_startup_options: The transformed list of startup_options to replace
          existing startup_options to be fed to the Bazel binary
        """

        parser = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
        self.add_startup_option_to_parser(parser)

        self.known_startup_options, self.user_startup_options = \
            parser.parse_known_args(self.startup_options)

        self.absolute_out_dir = self.workspace_dir / "out"
        self.absolute_user_root = \
            self.absolute_out_dir / "bazel/output_user_root"

        if self.known_startup_options.help:
            self.transformed_startup_options = [
                "--help"
            ]

        if not self.known_startup_options.help:
            javatmp = self.absolute_out_dir / "bazel/javatmp"
            self.transformed_startup_options = [
                f"--host_jvm_args=-Djava.io.tmpdir={javatmp}",
            ]

        # See _add_extra_startup_options for extra startup options

    def _parse_command_args(self):
        """Parses the given list of command_args.

        After calling this function, the following attributes are set:
        - known_args: A namespace holding options known by this Bazel wrapper script
        - transformed_command_args: The transformed list of command_args to replace
          existing command_args to be fed to the Bazel binary
        - env: A dictionary containing the new environment variables for the subprocess.
        """

        parser = argparse.ArgumentParser(add_help=False, allow_abbrev=False)

        # TODO: Delete these args once build bots no longer specify them
        parser.add_argument(
            "--make_jobs", metavar="JOBS", type=int, default=None,
            help="unused")
        parser.add_argument(
            "--make_keep_going", action="store_true", default=False,
            help="unused")
        parser.add_argument(
            "--repo_manifest", metavar="<repo_root>:<manifest.xml>",
            help="unused")

        # Skip startup options (before command) and target_patterns (after --)
        _, self.transformed_command_args = parser.parse_known_args(
            self.command_args)

    def _add_extra_startup_options(self):
        """Adds extra startup options after command args are parsed."""

        self.transformed_startup_options += self.user_startup_options

        if not self.known_startup_options.help:
            self.transformed_startup_options.append(
                f"--output_user_root={self.absolute_user_root}")

    def _build_final_args(self) -> list[str]:
        """Builds the final arguments for the subprocess."""
        # final_args:
        # bazel [startup_options] [additional_startup_options] command [transformed_command_args] -- [target_patterns]

        final_args = [self.bazel_path] + self.transformed_startup_options

        if self.command is not None:
            final_args.append(self.command)
        final_args += self.transformed_command_args
        if self.dash_dash is not None:
            final_args.append(self.dash_dash)
        final_args += self.target_patterns

        return final_args

    def run(self) -> int:
        """Runs the wrapper.

        Returns:
            doesn't return"""
        final_args = self._build_final_args()

        os.execve(path=self.bazel_path, argv=final_args, env=os.environ)


def _bazel_wrapper_main():
    # <workspace_dir>/bootable/libbootloader/gbl/bazel.py
    workspace_dir = (
        pathlib.Path(__file__).resolve().parent.parent.parent.parent)
    return BazelWrapper(workspace_dir=workspace_dir,
                        bazel_args=sys.argv[1:]).run()


if __name__ == "__main__":
    sys.exit(_bazel_wrapper_main())
