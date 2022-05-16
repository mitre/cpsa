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

## Composing a Release

[ ] Make sure changes are documented in CHANGELOG.md under Unreleased (in a separate commit)
[ ] Increment the version number appropriately in `package.json`
[ ] Regenerate `package-lock.json` to update this package's version number
    `npm install` will do this, but it will also rewrite `package.json` to change
    formatting. Keep the changes to `package-lock.json` but reset
    `package.json`.
[ ] Add a new heading to CHANGELOG.md with the version number
[ ] Add a new link to CHANGELOG.md to the new version on Artifactory
[ ] Add a new heading to README.md with the version number
[ ] Add a new link to README.md to the new version on Artifactory
[ ] Update the Installation section of README.md with the latest version
[ ] Make a commit with only these changes, titled "Release vscode-cpsa $VERSION"
[ ] Make sure working directory is clean, and build new package archive
    npm ci && vsce package
[ ] Upload the new archive to Artifactory (see section below)
[ ] Announce the new release

## Deploying to Artifactory

This project has a Repository on MITRE's Artifactory instance called
[`generic-vscode-cpsa-local`](https://artifacts.mitre.org/ui/repos/tree/General/generic-vscode-cpsa-local).
Developers with write access can upload new versions of the `.vsix`
archive, and anyone with a link to the repository can read all versions
without authentication.
Uploading files can be done through the web interface manually, as well as
with basic HTTP requests (with `curl` for example).

Steps for manual deploy via web browser:
    - Go to https://artifacts.mitre.org/ui/repos/tree/General/generic-vscode-cpsa-local
    - Click the Deploy button in the top right
    - Click Select File and select the new `.vsix` archive
    - Click Deploy
    - Artifactory should tell you whether it was successful, but you can also
      check by visiting the index here: https://artifacts.mitre.org/artifactory/generic-vscode-cpsa-local/ and looking for the new file you uploaded.

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
