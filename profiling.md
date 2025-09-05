# Profiling CPSA in this branch

First, install the profiling info for the Parallel package used by CPSA.

`cabal install -p --lib parallel --reinstall`

Enable profiling locally with 

`cabal configure --enable-profiling`.

Now, when you `make` a .txt from a .scm or .lsp, a `cpsa4.prof` file should be created.

### Debugging

If the above doesn't work, try running

`cabal update`

to update the local package list.


## Profiteur Visualization

Profiteur is a tree/box visaulization tool for Haskell profiling files.  To install, run

`cabal install profiteur`

Once installed, you may run

`profiteur cpsa4.prof`

or simply

`make cpsa4.prof.html`.
