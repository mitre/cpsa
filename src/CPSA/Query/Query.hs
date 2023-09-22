module CPSA.Query.Query (Query, loadQuery, execQuery) where

import System.IO
import CPSA.Lib.SExpr
import CPSA.Lib.Entry
import CPSA.Query.Tree

data Query
    = HasKey String
    deriving Show

loadQuery :: String -> IO (Query, [Int])
loadQuery file =
    do
      input <- openFile file ReadMode
      p <- posHandle file input
      q <- readSExpr p
      case q of
        Nothing -> fail "no query in query input"
        Just x ->
            do
              pq <- parseQuery x
              ints <- getInts p
              case ints of
                [] -> fail "no ints in query input"
                _ -> return (pq, ints)


parseQuery :: SExpr Pos -> IO Query
parseQuery (L _ [S _ "has-key", S _ sym]) = return (HasKey sym)
parseQuery _ = fail "query does not parse"
               
getInts :: PosHandle -> IO [Int]
getInts p =
    do 
      i <- readSExpr p
      case i of
        Nothing -> return []
        Just x ->
            case x of
              N _ n ->
                  do
                    rest <- getInts p
                    return (n:rest)
              _ -> fail "bad int in query file"
                      
execQuery :: (Query, [Int]) -> Forest -> IO [Int]
execQuery (_, ints) _ = return ints
