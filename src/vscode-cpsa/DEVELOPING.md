# Developing on this VSCode extension

## Conventions

This project uses [Keep a Changelog](https://keepachangelog.com/en/1.0.0)
and the [Semantic Versioning](https://semver.org/spec/v2.0.0.html) spec.

When adding new features, fixing bugs, and especially changing existing
functionality that users would notice, be sure to clearly document what
has changed and update the version number appropriately. Try to avoid
breaking any functionality if possible by making changes in a
backwards-compatible way.

Change logs should be added to `CHANGELOG.md`, written for a user
perspective. Focus on why a user would care that something changed, rather
than giving only technical details about internals. Copying text from git
commits is unlikely to be ideal here, because the intended audiences are
different.

The version number can be changed by editing `package.json`.

## Building the extension

You will need to have NPM installed, as well as the `vsce` NPM package.

    npm install --global vsce

This seems to be necessary to install the extension's dependencies to
`node_modules/`:

    npm install

To build a shareable `.vsix` archive, run

    vsce package

This will create a `vscode-cpsa-VERSION.vsix` file (where VERSION is the
current version) which can be shared and installed to VSCode on users'
machines.

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
