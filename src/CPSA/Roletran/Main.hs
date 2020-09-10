-- Main routine for cpsa4roletran

module Main (main) where

import System.IO
import CPSA.Lib.Entry
import CPSA.Lib.Expand
import CPSA.Roletran.Protocol
import CPSA.Roletran.Loader
import CPSA.Roletran.Derivation
import CPSA.Roletran.Emitter
import CPSA.Lib.Pretty (pr)

main :: IO ()
main =
    do
      (p, (output, margin)) <- start filterOptions filterInterp
      sexprs <- readSExprs p
      prot <- tryRun (loadSExprs sexprs)
      procs <- tryRun (mapM derive (roles prot))
      h <- outputHandle output
      hPutStrLn h ("(comment \"Protocol: " ++ pname prot ++
                   " (" ++ displayPos (ppos prot) ++ ")\")")
      mapM_ (emitProc h margin) procs
      hClose h

tryRun :: IO a -> IO a
tryRun x =
  do
    y <- tryIO x
    case y of
      Right z -> return z
      Left err -> abort err

emitProc :: Handle -> Int -> Proc -> IO ()
emitProc h margin proc =
  do
    hPutStrLn h ""
    hPutStrLn h ("(comment \"Role: " ++ name proc ++
                   " (" ++ displayPos (pos proc) ++ ")\")")
    hPutStrLn h ""
    hPutStrLn h $ pr margin (emit defaultIndent proc) ""
