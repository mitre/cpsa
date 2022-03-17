# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0),
and this project follows the [Semantic Versioning](https://semver.org/spec/v2.0.0.html) spec.

## Unreleased

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

[0.2.0]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.2.0.vsix
[0.1.0]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.1.0.vsix
