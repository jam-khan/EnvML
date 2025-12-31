module EnvML.Manager.Sort where

import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

type Node = FilePath
type Neighbours = [FilePath]
type Graph = M.Map Node Neighbours
type Queue = [FilePath]
type InDegree = M.Map Node Integer
type Count = Int
type SortOrder = [FilePath]
type Files = [FilePath]

{- | `getNodes` collects all nodes from the graph.

=== Example:
>>> getNodes cyclicGraph
["A","B","C"]
-}
getNodes ::
    Graph ->
    [FilePath]
getNodes graph = S.toList $ S.unions (M.keysSet graph : map S.fromList (M.elems graph))

{- | `reverseGraph` simply returns reversed graph

=== Example:
>>> reverseGraph cyclicGraph
fromList [("A",["C"]),("B",["A"]),("C",["B"])]

>>> reverseGraph validGraph
fromList [("B",["A"]),("C",["B","A"])]
-}
reverseGraph ::
    Graph ->
    Graph
reverseGraph graph =
    M.fromListWith
        (++)
        [(dep, [node]) | (node, deps) <- M.toList graph, dep <- deps]

{- | `in-degree` calculates the initial in-degree of all nodes

=== Example:
>>> inDegree (reverseGraph validGraph)
fromList [("A",1),("B",1),("C",0)]
-}
inDegree ::
    Graph ->
    InDegree
inDegree graph =
    M.fromListWith
        (+)
        [(dep, 1) | deps <- M.elems graph, dep <- deps]
        `M.union` M.fromList [(n, 0) | n <- getNodes graph]

{- | `initialQueue` is a utility function that returns the queue filled
with nodes of indegree 0.

=== Example:
>>> initialQueue (reverseGraph validGraph)
["C"]

>>> initialQueue (reverseGraph cyclicGraph)
[]
-}
initialQueue ::
    Graph ->
    [FilePath]
initialQueue graph = [file | (file, degree) <- M.toList (inDegree graph), degree == 0]

{- | `updateQueueInDegree` is a utility function that decrements in-degree
of each file present in the `Files` input and appends files with 0 in-degree
into the queue.

=== Example:
>>> updateQueueInDegree [] (inDegree (reverseGraph validGraph)) ["C"]
([],fromList [("A",1),("B",1),("C",-1)])

>>> updateQueueInDegree [] (inDegree (reverseGraph cyclicGraph)) ["C"]
(["C"],fromList [("A",1),("B",1),("C",0)])
-}
updateQueueInDegree ::
    Queue ->
    InDegree ->
    Files ->
    (Queue, InDegree)
updateQueueInDegree queue indegree [] = (queue, indegree)
updateQueueInDegree queue indegree (file : rest) =
    let
        newInDegree = M.adjust (subtract 1) file indegree
     in
        if fromMaybe 0 (M.lookup file newInDegree) == 0
            then
                updateQueueInDegree (queue ++ [file]) newInDegree rest
            else
                updateQueueInDegree queue newInDegree rest

{- | `topologicalSort` returns the topological sort of the graph

=== Example:
>>> topologicalSort [] (inDegree (reverseGraph validGraph)) validGraph 0 []
(0,[])
-}
topologicalSort ::
    Queue ->
    InDegree ->
    Graph ->
    Count ->
    SortOrder ->
    (Count, SortOrder)
topologicalSort [] _ _ count result = (count, result)
topologicalSort (curr : queue) indegree graph count result =
    let
        (newQueue, newInDegree) = updateQueueInDegree queue indegree (fromMaybe [] (M.lookup curr graph))
     in
        topologicalSort newQueue newInDegree graph (count + 1) (result ++ [curr])

{- | `getDependencyOrder` returns dependency resolution order of the modules.

=== Examples:
>>> getDependencyOrder validGraph
Right ["C","B","A"]
-}
getDependencyOrder ::
    Graph ->
    Either String [FilePath]
getDependencyOrder graph =
    let
        reversedGraph = reverseGraph graph
        queue = initialQueue reversedGraph
        (count, order) = topologicalSort queue (inDegree reversedGraph) reversedGraph 0 []
        totalNodes = length (getNodes graph)
        -- Add any missing nodes (isolated ones) in arbitrary order at the end
        allNodes = getNodes graph
        missingNodes = filter (`notElem` order) allNodes
     in
        if count + length missingNodes == totalNodes
            then
                Right (order ++ missingNodes)
            else
                Left "Cyclic dependencies detected."

-- Example 1
validGraph :: Graph
validGraph =
    M.fromList
        [ ("A", ["B"])
        , ("B", ["C"])
        , ("C", [])
        ]

-- Example 2
cyclicGraph :: Graph
cyclicGraph =
    M.fromList
        [ ("A", ["B"])
        , ("B", ["C"])
        , ("C", ["A"])
        ]

-- Example 3
validGraph2 :: Graph
validGraph2 =
    M.fromList
        [ ("A", [])
        , ("B", [])
        , ("C", [])
        ]
