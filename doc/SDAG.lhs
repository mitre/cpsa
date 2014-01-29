Strand Directed Acyclic Graphs

Run this with

  $ ghci SDAG.lhs

> module SDAG where

> import qualified Data.List as L
> import qualified Data.Set as S

The strands in a skeleton are represented by the natural numbers less
than the number of strands in the skeleton.  The strands in a
skeleton are describe by a list of integers, where each element of
the list gives the height of its strand.

> type Strands = [Int]          -- [Strand height]

A node is a pair of natural numbers.  The first number is the node's
strand, and the second is the position of the node within the strand.

> type Node = (Int, Int)        -- (Strand, Position)

Given a strand height list, the set of nodes are

> nodes :: Strands -> [Node]
> nodes heights =
>     [(s, p) | (s, n) <- zip [0..] hts, p <- nats n]
>     where hts = filter (0 <) heights -- remove non-positive heights

where nats n is the list of natural numbers less than n.

> nats :: Int -> [Int]
> nats n = take n [0..]

Thus for a skeleton with three strands, of height 2, 3, and 2, the
nodes are

  *SDAG> nodes [2,3,2]
  [(0,0),(0,1),(1,0),(1,1),(1,2),(2,0),(2,1)]

The edges in an SDAG represent the precedes relation.

> type Edge = (Node, Node)      -- Precedes relation

When (n0, n1) :: Edge, the message event at n0 precedes the one at n1.

The strand succession edges are

> successors :: Strands -> [Edge]
> successors heights =
>     [((s, p), (s, p + 1)) | (s, n) <- zip [0..] hts, p <- nats (n - 1)]
>     where hts = filter (0 <) heights -- remove non-positive heights

For a skeleton with three strands, of height 2, 3, and 2, the strand
succession edges are

  *SDAG> successors [2,3,2]
  [((0,0),(0,1)),((1,0),(1,1)),((1,1),(1,2)),((2,0),(2,1))]

A Strand Directed Acyclic Graph (SDAG) is a strand height list and a
set of edges.  It represents an acyclic graph.

> type SDAG = (Strands, [Edge])

The normalized form of a SDAG contains no strand succession edges or
elements in its transitive closure.

> normalize :: SDAG -> SDAG
> normalize (strands, precedes) =
>     if isAcyclic (adj sdag) ns then
>         sdag                  -- SDAG must be acyclic
>     else
>         error "SDAG has a cycle"
>     where
>       ns = nodes strands      -- Sort SDAG and remove duplicates
>       sdag = (strands, L.sort (L.nub prec))
>       prec = [(n0, n1) |
>               (n0, n1) <- precedes,
>               elem n0 ns,     -- Ensure n0 and n1 are in nodes
>               elem n1 ns,     -- Remove strand succession edges
>               not (sameStrands (n0, n1))]

> sameStrands :: Edge -> Bool
> sameStrands ((s0, _), (s1, _)) = s0 == s1

The adjacency list representation of an SDAG is used to map a node to
a list of its predecessors.  The adjacency list representation is
[[[Node]]], and lookup involves list indexing.  The representation of
an SDAG includes the strand succession edges.

> adj :: SDAG -> Node -> [Node]
> adj (strands, precedes) (s, p) =
>     [ strand s h | (s, h) <- zip [0..] strands ] !! s !! p
>     where
>       strand s h = [ entry (s, p) | p <- nats h ]
>       entry n = enrich n [ n0 | (n0, n1) <- precedes, n1 == n ]
>       -- add strand succession edges
>       enrich (s, p) ns
>           | p > 0 = (s, p - 1) : ns
>           | otherwise = ns

Is graph acyclic?

> isAcyclic :: Ord a => (a -> [a]) -> [a] -> Bool
> isAcyclic adj nodes =
>     all (not . backEdge numbering) (S.toList edges)
>     where
>       numbering = dfs adj (S.toList start)
>       -- Remove nodes that have non-zero indegree
>       start = S.difference (S.fromList nodes) (S.map fst edges)
>       edges = foldl f S.empty nodes
>       f edges src = foldl (g src) edges (adj src)
>       g src edges dst = S.insert (dst, src) edges

Compute a depth first search numbering of nodes using postorder.
With postorder, only back edges go from a lower number to a higher
one.  Assumes nodes, the set of nodes with indegree zero, is not empty.

> dfs :: Ord a => (a -> [a]) -> [a] -> [(a, Int)]
> dfs adj nodes =
>     alist
>     where
>       (_, alist, _) = foldl po (0, [], S.empty) nodes
>       po a@(num, alist, seen) node
>          | S.member node seen = a
>          | otherwise =
>              (num' + 1, (node, num') : alist', seen'')
>              where  -- Search is postorder because nodes at the end of
>                (num', alist', seen'') = -- edges are explored before
>                    foldl po (num, alist, seen') nodes' -- the node
>                seen' = S.insert node seen -- Insert node as soon as
>                nodes' = adj node          -- it's seen

Is edge a back edge, meaning a cycle has been found?  If an edge
contains a node that is not in the alist, it means it was not
visited during the depth first seach.  This can happen when there
is a strong component that has no edges from other strong
components to it.  We report this edge to be a back edge so as to
get the correct overall result.

> backEdge :: Eq a => [(a, Int)] -> (a, a) -> Bool
> backEdge alist (node, node') =
>     case (lookup node alist, lookup node' alist) of
>       (Just n, Just n') -> n >= n'
>       _ -> True

Compute the transitive reduction

> reduce :: SDAG -> SDAG
> reduce g@(strands, precedes) =
>     (strands, filter essential precedes)
>     where
>       essential (dst, src) =
>           loop dst (L.delete dst (adj g src)) [src]
>       loop _ [] _ = True        -- No other path found
>       loop dst (n : ns) seen
>           | n == dst = False    -- There is another path
>           | elem n seen = loop dst ns seen
>           | otherwise = loop dst (adj g n ++ ns) (n : seen)

Compute the transitive closure

> close :: SDAG -> SDAG
> close g@(strands, precedes) =
>     normalize (strands, loop prec False prec)
>     where
>       prec = successors strands ++ precedes
>       loop prec False [] = prec
>       loop prec True [] =
>           loop prec False prec -- restart loop
>       loop prec repeat ((n0, n1) : pairs) =
>           inner prec repeat pairs [(n, n1) | n <- adj g n0]
>       inner prec repeat pairs [] =
>           loop prec repeat pairs
>       inner prec repeat pairs (p : rest)
>           | elem p prec = inner prec repeat pairs rest
>           | otherwise = inner (p : prec) True pairs rest

Shorthands that check their arguments.

> r :: SDAG -> SDAG
> r = reduce . normalize

> c :: SDAG -> SDAG
> c = close . normalize

Is x a proper sublist of y?

> sublist :: Eq a => [a] -> [a] -> Bool
> sublist x y =
>     all (flip elem y) x &&    -- All x in y
>     any (flip notElem x) y    -- Some y not in x

The list of all sublists

> sublists :: [a] -> [[a]]
> sublists [] = [[]]
> sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)

Compute all the SDAGs that are weaker than the given SDAG.

> w :: SDAG -> [SDAG]
> w sdag =
>     let (s, es) = c sdag in
>     L.nub [r |
>            es0 <- sublists es,
>            let r = reduce (s, es0),
>            let (_, es1) = close (s, snd r),
>            sublist es1 es]

Examples

  *SDAG> w ([2,2], [((0,0),(1, 1))])
  [([2,2],[])]

  *SDAG> w ([2,2], [((0,1),(1, 0))])
  [([2,2],[]),
   ([2,2],[((0,1),(1,1))]),
   ([2,2],[((0,0),(1,1))]),
   ([2,2],[((0,0),(1,0))]),
   ([2,2],[((0,0),(1,0)),((0,1),(1,1))])]

Compute the SDAGs in w x that are not weaker than a SDAG in w x.

> m :: SDAG -> [SDAG]
> m sdag =
>     map reduce (filter maximal sdags)
>     where
>       sdags = map close (w sdag) -- All weaker SDAGs
>       maximal sdag =          -- Is SDAG not weaker than some other
>           not (any (weaker sdag) sdags)
>       weaker (s0, es0) (s1, es1) =
>           s0 == s1 && sublist es0 es1

Examples

  *SDAG> m ([2,2], [((0,0),(1, 1))])
  [([2,2],[])]

  *SDAG> m ([2,2], [((0,1),(1, 0))])
  [([2,2],[((0,0),(1,0)),((0,1),(1,1))])]

Compute the SDAGs in w x that are not weaker than a SDAG in w x using
the implemented algorithm.

> m' :: SDAG -> [SDAG]
> m' sdag =
>     let (s, es) = c sdag in
>     L.nub [reduce (s, L.delete e es) | e <- snd (reduce sdag)]

Read and show for CPSA orderings

> data O = O [Edge]

> instance Show O where
>    showsPrec _ (O es) =
>         showString "(precedes" . showl es
>         where
>           showl [] = showChar ')'
>           showl (e : es) = showChar ' ' . shows (E e) . showl es

> instance Read O where
>     readsPrec _ s0 =
>         [(O ord, s3) |
>          ("(", s1) <- lex s0,
>          ("precedes", s2) <- lex s1,
>          (ord, s3) <- readl s2]
>         where
>           readl s0 = [([], s1) |
>                       (")", s1) <- lex s0] ++
>                      [(e : es, s2) |
>                       (E e, s1) <- reads s0,
>                       (es, s2) <- readl s1]

A guess at the strand height list associated with some edges

> strands :: [Edge] -> Strands
> strands es =
>     [height s | s <- nats n]
>     where
>       n = 1 + foldl max 0 (map fst nodes)
>       nodes = L.nub (foldl (\ns (n0, n1) -> n0 : n1 : ns) [] es)
>       height s = 1 + foldl max 0 [p | (s', p) <- nodes, s' == s]

Read and show for edges

> data E = E Edge

> instance Show E where
>     showsPrec _ (E (n0, n1)) =
>         showChar '(' . shows (N n0) . showChar ' ' .
>                 shows (N n1) . showChar ')'

> instance Read E where
>     readsPrec _ s0 =
>         [(E (n0, n1), s4) |
>          ("(", s1) <- lex s0,
>          (N n0, s2) <- reads s1,
>          (N n1, s3) <- reads s2,
>          (")", s4) <- lex s3]

Read and show for nodes

> data N = N Node

> instance Show N where
>     showsPrec _ (N (s, p)) =
>         showChar '(' . shows s . showChar ' ' . shows p . showChar ')'

> instance Read N where
>     readsPrec _ s0 =
>         [(N (s, p), s4) |
>          ("(", s1) <- lex s0,
>          (s, s2) <- reads s1,
>          (p, s3) <- reads s2,
>          (")", s4) <- lex s3]
