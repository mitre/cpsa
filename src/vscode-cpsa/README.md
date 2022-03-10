# CPSA language support for Visual Studio Code

This extension adds support for CPSA to VS Code.

## Features

- Syntax highlighting based on Scheme syntax, with CPSA keywords added.
- Parentheses matching.
- A button added to the top-right of the editor pane, when editing a file
  detected as CPSA source code (`.scm`, `.lsp`). The button will build the
  output `.txt`, `.xhtml`, and `_shapes.txt` files for the
  currently-edited CPSA file. The file names are compatible with existing
  Makefile conventions used with CPSA4.
- When the CPSA source has errors, the messages are parsed so that the
  user can see where in the code an error was found.

## Requirements

The extension requires that CPSA4 be installed.
VSCode needs to be able to call the `cpsa4`, `cpsa4graph`, and
`cpsa4shapes` binaries.

The extension currently depends on features from VSCode 1.54 (February
2021) or newer.

## Installation

To obtain the built extension, you can build it from source or obtain a
`.vsix` archive. The latest version can be downloaded from Artifactory
here: [0.1.0]. See the "Building the extension" section of DEVELOPING.md
to build it from source.

To install the `.vsix` archive, there are two methods.

On the commandline, if the VSCode `code` executable is on your PATH:

    code --install-extension vscode-cpsa-VERSION.vsix

The other method is to use VSCode to "Open Folder" on the directory
containing the archive. Then, it should be possible to right-click the
file in VSCode's Explorer panel, and an "Install Extension" option should
be available.

If you already had the extension installed and you are replacing it,
VSCode might need to be restarted.

## Known Issues

This extension assumes that CPSA is installed. If it isn't, there will be
OS-specific error messages when it tries to run CPSA.

## Developing on this extension

Please see the DEVELOPING file.

## Release Notes

Recent releases will be mentioned in this section of the README;
all release history can be found in the CHANGELOG.

This extension follows the [Semantic Versioning](https://semver.org/spec/v2.0.0.html) spec.
This means that version numbers look like `MAJOR.MINOR.PATCH`.

From a user's perspective:

- If the MAJOR part has been incremented, then breaking changes have been
  made. This could include commands working differently in an incompatible
  way, or features being removed. Be careful updating to a new MAJOR
  release.
- If the MINOR part has been incremented, then features have been added
  without breaking compatibility. It should be safe to update to a new
  MINOR release.
- If the PATCH part has been incremented, then only bugfixes or
  user-invisible changes have been made. It should be safe to update to a
  new PATCH release.
- Until version 1.0.0, no compatibility guarantees are made. Versions
  before 1.0.0 are considered experimental.

### [0.1.0] - 2022-03-08

#### Added

- The build button now also generates a `_shapes.txt` output file, using
  `cpsa4shapes`.

### 0.0.1 - 2022-03-07

Initial testing release.

#### Added

- Syntax highlighting.
- Parentheses matching.
- A button to build the output `.txt` and `.xhtml` files with `cpsa4` and
  `cpsa4graph`, respectively.
- The errors from CPSA are detected with a Problem Matcher, to integrate
  with VSCode's built in error-highlighting features.

[0.1.0]: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/vscode-cpsa-0.1.0.vsix
