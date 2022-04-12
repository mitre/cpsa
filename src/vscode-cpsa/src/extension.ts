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
        'vscode-cpsa.execCPSACurrentFile',
        uri => executeFile(uri)
    );
    context.subscriptions.push(disposable);
}

const cpsa3_paths = {
    'cpsa': 'cpsa',
    'cpsashapes': 'cpsashapes',
    'cpsagraph': 'cpsagraph'
};

const cpsa4_paths = {
    'cpsa': 'cpsa4',
    'cpsashapes': 'cpsa4shapes',
    'cpsagraph': 'cpsa4graph'
};

// Run CPSA on a specific source file to generate the `.txt`, `.xhtml` and
// `_shapes.txt` output files, just like the conventional CPSA Makefile
// would create.
// This function is set up to be triggered by the
// `vscode-cpsa.execCPSACurrentFile` command.
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
    let out_shapes_xhtml = parsed.name + '_shapes.xhtml';

    let config = vscode.workspace.getConfiguration('CPSA.build');
    let compilerVersion = config.get('compilerVersion');

    let cpsa_paths = undefined;
    switch (compilerVersion) {
        case 'cpsa3':
            cpsa_paths = cpsa3_paths;
            break;
        case 'cpsa4':
            cpsa_paths = cpsa4_paths;
            break;
        default:
            // Default to CPSA 3 paths.
            // TODO print a warning
            cpsa_paths = cpsa3_paths;
            break;
    }

    let txt_task = new vscode.Task(
        {'type': 'cpsabuild_txt'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        `${cpsa_paths.cpsa} on current file`,
        'cpsabuild_txt',
        new vscode.ProcessExecution(cpsa_paths.cpsa, ['-o', out_txt, source]),
        // Refers to a Problem Matcher defined in `package.json`
        '$cpsabuild_txt'
    );
    await wait_for_task(txt_task);

    let xhtml_task = new vscode.Task(
        {'type': 'cpsabuild_xhtml'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        `${cpsa_paths.cpsagraph} on generated .txt`,
        'cpsabuild_xhtml',
        new vscode.ProcessExecution(cpsa_paths.cpsagraph, ['-o', out_xhtml, out_txt]),
        // Refers to a Problem Matcher defined in `package.json`
        '$cpsabuild_xhtml'
    );
    await wait_for_task(xhtml_task);

    let shapes_task = new vscode.Task(
        {'type': 'cpsabuild_shapes'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        `${cpsa_paths.cpsashapes} on generated .txt`,
        'cpsabuild_shapes',
        new vscode.ProcessExecution(cpsa_paths.cpsashapes, ['-o', out_shapes, out_txt]),
        // Refers to a Problem Matcher defined in `package.json`
        '$cpsabuild_shapes'
    );
    await wait_for_task(shapes_task);

    let shapes_xhtml_task = new vscode.Task(
        {'type': 'cpsabuild_shapes_xhtml'},
        vscode.TaskScope.Workspace,
        // User-visible name of this Task
        `${cpsa_paths.cpsagraph} on generated _shapes.txt`,
        'cpsabuild_shapes_xhtml',
        new vscode.ProcessExecution(cpsa_paths.cpsagraph, ['-o', out_shapes_xhtml, out_shapes]),
        // Refers to a Problem Matcher defined in `package.json`
        '$cpsabuild_shapes_xhtml'
    );
    await wait_for_task(shapes_xhtml_task);
}

async function wait_for_task(task: vscode.Task) {
    const execution = await vscode.tasks.executeTask(task);

    return new Promise<void>(resolve => {
        let disposable = vscode.tasks.onDidEndTask(e => {
            if (e.execution === execution) {
                disposable.dispose();
                resolve();
            }
        });
    });
}

// This method is called when the extension is deactivated.
export function deactivate() {}
