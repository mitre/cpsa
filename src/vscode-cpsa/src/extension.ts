import * as path from 'path';
import * as vscode from 'vscode';

// This method is called when the extension is activated.
export function activate(context: vscode.ExtensionContext) {

    // The command has been defined in the package.json file.
    // Now the implementation of the command is set up with
    // registerCommand.
    // The commandId parameter must match the command field in
    // package.json.
    let disposable = vscode.commands.registerCommand(
        'vscode-cpsa.execCPSA4CurrentFile',
        uri => executeFile(uri)
    );
    context.subscriptions.push(disposable);
}

// Run CPSA on a specific source file to generate the `.txt`, `.xhtml` and
// `_shapes.txt` output files, just like the conventional CPSA4 Makefile
// would create.
// This function is set up to be triggered by the
// `vscode-cpsa.execCPSA4CurrentFile` command.
//
// This works by creating ephemeral `Task`s, and immediately running them
// with `vscode.tasks.executeTask()`. Normally an extension informs VSCode
// about build tasks using the `TaskProvider` interface, but that is not
// ideal for the CPSA use case where each source file is usually
// self-contained and there is not really a central build system or source
// heirarchy like most languages.
async function executeFile(uri: vscode.Uri) {
    let file_path = uri.fsPath;
    // Split the file path to remove the file extension of the source
    // file.
    let parsed = path.parse(file_path);
    let source = parsed.base;
    // Generate the output file names by adding conventional suffixes.
    let out_txt = parsed.name + '.txt';
    let out_xhtml = parsed.name + '.xhtml';
    let out_shapes = parsed.name + '_shapes.txt';

    let txt_task = new vscode.Task(
        {'type': 'cpsa4build'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        'cpsa4 on current file',
        'cpsa4build',
        new vscode.ProcessExecution('cpsa4', ['-o', out_txt, source]),
        // Refers to the `cpsa4` Problem Matcher defined in `package.json`
        '$cpsa4'
    );
    await vscode.tasks.executeTask(txt_task);

    let xhtml_task = new vscode.Task(
        {'type': 'cpsa4build'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        'cpsa4graph on generated .txt',
        'cpsa4build',
        new vscode.ProcessExecution('cpsa4graph', ['-o', out_xhtml, out_txt]),
        // Refers to the `cpsa4` Problem Matcher defined in `package.json`
        '$cpsa4'
    );
    await vscode.tasks.executeTask(xhtml_task);

    let shapes_task = new vscode.Task(
        {'type': 'cpsa4build'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        'cpsa4shapes on generated .txt',
        'cpsa4build',
        new vscode.ProcessExecution('cpsa4shapes', ['-o', out_shapes, out_txt]),
        // Refers to the `cpsa4` Problem Matcher defined in `package.json`
        '$cpsa4'
    );
    await vscode.tasks.executeTask(shapes_task);
}

// This method is called when the extension is deactivated.
export function deactivate() {}
