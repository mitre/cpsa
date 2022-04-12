# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0),
and this project follows the [Semantic Versioning](https://semver.org/spec/v2.0.0.html) spec.

## Unreleased

### Added

- The extension now runs `cpsa`/`cpsa4` with the appropriate RTS flags to
  enable multithreading and limit GHC's runtime heap size to prevent
  whole-system hangs. The heap size limit is configurable in the Settings
  menu, and defaults to 512 MB.

### Fixed

- Error squiggles are fixed. This was unexpectedly broken in version 0.2.1 due
  to that fix serializing all build steps, allowing VSCode to use an
  undocumented heuristic that causes error squiggles to be cleared when a
  Problem Matcher gets re-used. Users may have seen an error squiggle briefly
  appear, but then disappear right when a subsequent build step ran.

  This release fixes error squiggles by simply making copies of the Problem
  Matcher for each different build step. All error squiggles caused by
  different build steps should persist until re-running the whole set, as
  expected.

  All build steps are still attempted, regardless of whether an earlier one
  fails.

## [0.3.0] - 2022-03-28

Breaking change: The extension now defaults to using CPSA version 3 rather
than 4. Users who use CPSA4 will need to
[change the setting](https://code.visualstudio.com/docs/getstarted/settings#_settings-editor)
under Settings -> Extensions -> CPSA. The setting is called "Build: Compiler
Version".

### Added

- The extension can now make use of both CPSA 3 and 4, switching between them
  with a configuration setting. The default is set to CPSA 3.

## [0.2.1] - 2022-03-18

### Fixed

- The extension did not properly wait for Tasks to finish before starting
  later ones which depended on them completing. This led to corrupted or
  incomplete results. Now all tasks are executed serially in a predictable
  order.

## [0.2.0] - 2022-03-17

### Added

- The build button now also generates a `_shapes.xhtml` output file, using
  `cpsa4graph`, from the `_shapes.txt` generated file.

### Fixed

- The extension now calls `cpsa4` and other tools with relative paths. This is
  a workaround for the fact that CPSA cannot currently handle backslashes in
  strings due to Windows absolute file paths.

## [0.1.0] - 2022-03-08

### Added

- The build button now also generates a `_shapes.txt` output file, using
  `cpsa4shapes`.

## 0.0.1 - 2022-03-07

Initial testing release.

### Added

- Syntax highlighting.
- Parentheses matching.
- A button to build the output `.txt` and `.xhtml` files with `cpsa4` and
  `cpsa4graph`, respectively.
- The errors from CPSA are detected with a Problem Matcher, to integrate
  with VSCode's built in error-highlighting features.

[0.3.0]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.3.0.vsix
[0.2.1]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.2.1.vsix
[0.2.0]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.2.0.vsix
[0.1.0]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.1.0.vsix
