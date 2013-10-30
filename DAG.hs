module DAG
  (  
     -- ^ Constructs
     GraphData
   , GraphSkel
   , GraphInitFun
   , GraphStepFun
   , GraphResultFun
   , GraphResult
     
     -- ^ Run functions
   , graphAlgorithm
   , cycle
   , occur  
  ) where

import Prelude hiding (cycle)
import Data.List (nub, groupBy, sortBy, span)
import Data.Function (on)

-- Remove:
import Data.Map (Map)
import Data.ListTrie.Patricia.Map (TrieMap)

import qualified Data.ListTrie.Patricia.Map as P
import qualified Data.Map                   as Map
-- End of Remove

--------------------------------------------------------------------------------
--
--                                 Constructs
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--                                                   * Graph algorithm generator

-- | Input data for graph algorithm
type GraphData id = (id,     id   )
                 -- (parent, child)

-- | Skeleton node of graph
type GraphSkel id = (id, [id],    [id]    )
                 -- (id, parents, children)

-- | Node of the graph, not exported
type GraphNode id c = (id, [c]  ) 
                   -- (id, chain)

-- | Init function of the iteration
type GraphInitFun id c = Int  -> [id] -> id -> c
                      -- size -> ids  -> id -> init

-- | Step function of the iteration
type GraphStepFun c = c    -> [c]     -> [c]      -> c
                   -- prev -> parents -> children -> next 

-- | Function to compute the result
type GraphResultFun id c r = Int  -> [id] -> [c]   -> r
                          -- size -> ids  -> chain -> result

-- | Result of the algorithm
type GraphResult id r = (id, r     )
                     -- (id, result)

--------------------------------------------------------------------------------
--
--                               Functions
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--                                                              * Pair functions

pairToList   :: (a, a) -> [a]
pairToList   (a, b) = [a, b]

eqFst, eqSnd :: (Eq a) => a -> (a, a) -> Bool
eqFst        a (b, _) = a == b
eqSnd        a (_, b) = a == b

--------------------------------------------------------------------------------
--                                                        * Graph node functions

eqNode       :: (Eq id) => id -> GraphNode id c -> Bool
eqNode       key (id, _)  = key == id

getNode      :: (Eq id) => [GraphNode id c] -> id -> GraphNode id c 
getNode      nodes key = head . filter (eqNode key) $ nodes

getId        :: (Eq id) => GraphNode id c -> id
getId        = fst

getChain     :: (Eq id) => GraphNode id c -> [c] 
getChain     = snd

--------------------------------------------------------------------------------
--
--                                  Algorithm
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--                                                            * Graph Algorithms

-- | Applies the graph algorithm
graphAlgorithm :: (Eq id) => 
                     [GraphData id]          -- ^ edges
                  -> GraphInitFun id c       -- ^ init function
                  -> GraphStepFun c          -- ^ step   -||-
                  -> GraphResultFun id c r   -- ^ result -||-
                  -> [GraphResult id r]      -- ^ result
graphAlgorithm edges init step goal = result
  where
    ids  = nub . concat . map pairToList $ edges
    size = length ids

    skeletonNodes = map makeSkeletonNode ids
      where
        makeSkeletonNode id = (id, parentIds, childIds)
          where parentIds = map fst . filter (eqSnd id) $ edges
                childIds  = map snd . filter (eqFst id) $ edges
  
    graph = map makeGraphNode $ skeletonNodes
      where    
        makeGraphNode (id, parentIds, childIds) = (id, chain)
          where
            parentChains = map (getChain . getNode graph) parentIds
            childChains  = map (getChain . getNode graph) childIds
        
            chain = hd : tl
              where hd = init size ids id
                    tl = next hd parentChains childChains
        
            next prev parents children = curr : rest
              where curr = step prev (map head parents) (map head children)
                    rest = next curr (map tail parents) (map tail children)
    
    result = map makeResult $ graph
      where
        makeResult (id, chain) = (id, goal size ids chain)
        
--------------------------------------------------------------------------------
--                                                 ** Graph acyclicity algorithm

-- | Finds cycles in a graph
cycle :: (Eq id) => [GraphData id] -> [GraphResult id Bool]
cycle edges = graphAlgorithm edges init step result
  where
    maximum' [] = 0
    maximum' xs = maximum xs
    
    init :: (Eq id) => Int -> [id] -> id -> Int
    init _ _ _ = 1
    
    step :: Int -> [Int] -> [Int] -> Int
    step _ parents _ = maximum' parents + 1
    
    result :: (Eq id) => Int -> [id] -> [Int] -> Bool
    result size _ chain = convergence chain
      where 
        convergence :: [Int] -> Bool
        convergence (x:y:_) | x == y   = True
        convergence (x:_)   | x > size = False
        convergence (_:x)              = convergence x
        
--------------------------------------------------------------------------------
--                                               ** Graph reachability algorithm

occur :: (Eq id) => [GraphData id] -> GraphData id -> GraphData id -> [GraphResult id Bool]
occur edges parent child = graphAlgorithm edges init step result
  where
    maximum' [] = 0
    maximum' xs = maximum xs
    
    init :: (Eq id) => Int -> [id] -> id -> Int
    init _ _ id | id == parent = 1
                | otherwise    = 0
    
    step :: Int -> [Int] -> [Int] -> Int
    step _ parents _ =  
    
    result :: (Eq id) => Int -> [id] -> [Int] -> Bool
    result = undefined
    
    
--------------------------------------------------------------------------------
--
--                                  Testing
--
--------------------------------------------------------------------------------

a :: P.TrieMap Map.Map Char Int
a = P.insert "harro" 20
  $ P.singleton "harry" 99
  
createTrie :: (Ord a) =>  [(a, b)] -> P.TrieMap Map.Map Char Int
createTrie xs = undefined
  where
     xs' = groupBy ((==) `on` fst) . sortBy (compare `on` fst) xs
     