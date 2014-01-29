> module Main (main) where

> import System.Time (ClockTime(..), getClockTime)
> import Data.Tree (Tree(..), flatten)
> import Data.Maybe (isNothing)

The reduction system takes a rule, a step count, and an initial value,
and computes a tree of reductions.

> reduce :: (Eq a, Monad m) => (a -> [a]) -> Int -> a -> m (Tree a)
> reduce rule limit root =
>     step rule limit [top] [top]
>     where
>      top = Item { item = root, parent = Nothing }

The Item data structure stores the information about a reduction step
in a form that can be used to construct the final answer as a tree.

> data Eq a => Item a
>     = Item { item :: a,
>              parent :: Maybe (Item a) }

> instance Eq a => Eq (Item a) where
>     x == y = item x == item y

The step function is where nearly all of the time is used.  It is
called as:

  step rule limit seen todo

where seen is the items already seen, and todo is the items on the
queue.  The order of the items in the seen list is irrelevant, because
the tree is assembled as a post processing step.

> step :: (Eq a, Monad m) => (a -> [a]) -> Int ->
>         [Item a] -> [Item a] -> m (Tree a)
> step _ limit _ _
>     | limit <= 0 = fail "Step limit exceeded"
> step _ _ seen [] = tree seen
> step rule limit seen (next : rest) =
>     loop seen rest children
>     where
>      children = map child (rule (item next))
>      child i = Item { item = i, parent = Just next }
>      loop seen rest [] =
>          step rule (limit - 1) seen rest
>      loop seen rest (kid : kids) =
>          if elem kid seen then
>             loop seen rest kids
>          else
>             loop (kid : seen) (rest ++ [kid]) kids

The next two functions assemble the answer into a tree.
Sequential search is just fine for tree building.

> tree :: (Eq a, Monad m) => [Item a] -> m (Tree a)
> tree items =
>     case filter (isNothing . parent) items of
>       [root] -> return (build items (item root))
>       _ -> fail "bad tree"

> build :: Eq a => [Item a] -> a -> Tree a
> build items root =
>     Node { rootLabel = root,
>            subForest = map (build items . item) children }
>     where
>       children = filter child items
>       child i = maybe False ((== root) . item) (parent i)

A silly rule

> rule :: Int -> [Int]
> rule n = filter (>= 0) [n - 1, n `quot` 2, n `quot` 3]

> secDiff :: ClockTime -> ClockTime -> Float
> secDiff (TOD secs1 psecs1) (TOD secs2 psecs2)
>     = fromInteger (psecs2 - psecs1) / 1e12 + fromInteger (secs2 - secs1)

> main :: IO ()
> main =
>     do
>       t0 <- getClockTime
>       t <- reduce rule 20000 5000
>       let ns = length (flatten t)
>       t1 <- getClockTime
>       putStrLn $ "length: " ++ show ns
>       putStrLn $ "time: " ++ show (secDiff t0 t1) ++ " seconds"

The makefile
------------
PROG	= reduce
GHCFLAGS = -Wall -package containers -fno-warn-name-shadowing -O

%:	%.lhs
	ghc $(GHCFLAGS) -o $@ $<

all:	$(PROG)

clean:
	-rm *.o *.hi $(PROG)
