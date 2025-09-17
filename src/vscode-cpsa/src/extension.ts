import * as path from 'path';
import * as vscode from 'vscode';

// This method is called when the extension is activated.
export function activate(context: vscode.ExtensionContext) {

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

async function executeFile(uri?: vscode.Uri) {
    let file_path = '';
    if (uri) {
        file_path = uri.fsPath;
    } else {
        const editor = vscode.window.activeTextEditor;
        if (!editor) return;
        file_path = editor.document.fileName;
    }

    const parsed = path.parse(file_path); // file info
    const source = parsed.base; // filename only

    // output files
    const out_txt = parsed.name + '.txt';
    const out_xhtml = parsed.name + '.xhtml';
    const out_shapes = parsed.name + '_shapes.txt';
    const out_shapes_xhtml = parsed.name + '_shapes.xhtml';

    const config = vscode.workspace.getConfiguration('CPSA.build');
    const compilerVersion = config.get<string>('compilerVersion');

    let cpsa_paths = cpsa4_paths; // default to CPSA4
    if (compilerVersion === 'cpsa3') cpsa_paths = cpsa3_paths;

    let ghcMemLimitMegabytes = config.get<number>('ghcMemLimitMegabytes') || 512;
    const rtsOpts = [
        '+RTS',
        '-N',
        `-M ${ghcMemLimitMegabytes}m`,
        '-RTS'
    ];

    // Run cpsa -> .txt
    const txt_task = new vscode.Task(
        { type: 'cpsabuild_txt' },
        vscode.TaskScope.Workspace,
        `${cpsa_paths.cpsa} on current file`,
        'cpsabuild_txt',
        new vscode.ProcessExecution(cpsa_paths.cpsa, [...rtsOpts, '-o', out_txt, source], { cwd: parsed.dir }),
        '$cpsabuild_txt'
    );
    await wait_for_task(txt_task);

    // Run cpsagraph -> .xhtml
    const xhtml_task = new vscode.Task(
        { type: 'cpsabuild_xhtml' },
        vscode.TaskScope.Workspace,
        `${cpsa_paths.cpsagraph} on generated .txt`,
        'cpsabuild_xhtml',
        new vscode.ProcessExecution(cpsa_paths.cpsagraph, ['-o', out_xhtml, out_txt], { cwd: parsed.dir }),
        '$cpsabuild_xhtml'
    );
    await wait_for_task(xhtml_task);

    // Run cpsashapes -> _shapes.txt
    const shapes_task = new vscode.Task(
        { type: 'cpsabuild_shapes' },
        vscode.TaskScope.Workspace,
        `${cpsa_paths.cpsashapes} on generated .txt`,
        'cpsabuild_shapes',
        new vscode.ProcessExecution(cpsa_paths.cpsashapes, ['-o', out_shapes, out_txt], { cwd: parsed.dir }),
        '$cpsabuild_shapes'
    );
    await wait_for_task(shapes_task);

    // Run cpsagraph -> _shapes.xhtml
    const shapes_xhtml_task = new vscode.Task(
        { type: 'cpsabuild_shapes_xhtml' },
        vscode.TaskScope.Workspace,
        `${cpsa_paths.cpsagraph} on generated _shapes.txt`,
        'cpsabuild_shapes_xhtml',
        new vscode.ProcessExecution(cpsa_paths.cpsagraph, ['-o', out_shapes_xhtml, out_shapes], { cwd: parsed.dir }),
        '$cpsabuild_shapes_xhtml'
    );
    await wait_for_task(shapes_xhtml_task);
}

async function wait_for_task(task: vscode.Task) {
    const execution = await vscode.tasks.executeTask(task);

    return new Promise<void>(resolve => {
        const disposable = vscode.tasks.onDidEndTask(e => {
            if (e.execution === execution) {
                disposable.dispose();
                resolve();
            }
        });
    });
}

// This method is called when the extension is deactivated.
export function deactivate() {}
