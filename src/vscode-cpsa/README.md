# CPSA language support for Visual Studio Code

This extension adds support for CPSA to VS Code.

## Features

- Syntax highlighting based on Scheme syntax, with CPSA keywords added.
- Parentheses matching.
- A button added to the top-right of the editor pane, when editing a file
  detected as CPSA source code (`.scm`, `.lsp`). The button will build the
  output `.txt`, `.xhtml`, and `_shapes.txt` files for the
  currently-edited CPSA file. The file names are compatible with existing
  Makefile conventions used with CPSA.
- A default keybinding of `Ctrl+Shift+B` (Windows, Linux) or `Cmd+Shift+B`
  (Mac) that triggers the same build functionality as the button.
- When the CPSA source has errors, the messages are parsed so that the
  user can see where in the code an error was found.

## Requirements

The extension requires that CPSA be installed. Both CPSA 3 and CPSA 4 are
supported.  VSCode needs to be able to call the `cpsa`, `cpsagraph`, and
`cpsashapes` binaries. For CPSA 4, these are named `cpsa4`, `cpsa4graph`,
and `cpsa4shapes`, respectively.
The extension needs to be configured for which CPSA version you have
installed. Version 3 is the default. First
[go to the Settings menu](https://code.visualstudio.com/docs/getstarted/settings#_settings-editor)
and then select Extensions -> CPSA to find the "Build: Compiler Version"
setting.

The extension currently depends on features from VSCode 1.54 (February
2021) or newer.

## Installation

To obtain the built extension, you can build it from source or obtain a
`.vsix` archive. See the "Building the extension" section to build it from
source.

To install the `.vsix` archive, there are two methods.

On the commandline, if the VSCode `code` executable is on your PATH:

    code --install-extension vscode-cpsa-VERSION.vsix

The other method is to use VSCode to "Open Folder" on the directory
containing the archive. Then, it should be possible to right-click the
file in VSCode's Explorer panel, and an "Install Extension" option should
be available.

If you already had the extension installed and you are replacing it,
VSCode might need to be restarted.

## Building the extension

You will need to have NPM installed, as well as the `vsce` NPM package.

    npm install --global vsce

This step is necessary to install the extension's dependencies to
`node_modules/`:

    npm install

To build a shareable `.vsix` archive, run

    vsce package

This will create a `vscode-cpsa-VERSION.vsix` file (where VERSION is the
current version) which can be shared and installed to VSCode on users'
machines.

## Known Issues

This extension assumes that CPSA is installed. If it isn't, there will be
OS-specific error messages when it tries to run CPSA.

## Release Notes

All release history can be found in the CHANGELOG.

## Code Overview

`package.json`: This is both a standard NPM package description file, as
well as the location to declaratively configure many aspects of a VSCode
extension.  This often works by declaring that the extension contributes
something and doing some of the configuration directly in `package.json`,
but more of the implementation is in another configuration file or is done
in Typescript code.

`cpsa.language-configuration.json`: This is a straightforward declarative
file that configures basic syntax features like comments and which symbols
match each other (such as parentheses and brackets).

`syntaxes/cpsa.tmLanguage`: This is a TextMate XML file that defines a
language syntax. If the syntax of CPSA is changed, such as by adding or
removing keywords, this file would need to be edited.

`src/extension.ts`: This is a Typescript source file and is the entry
point to the code of the extension.  This is where the build functionality
is implemented.
