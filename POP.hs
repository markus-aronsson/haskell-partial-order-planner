{-#LANGUAGE GADTs, KindSignatures #-}

module POP where

import DAG
import FOL

import Control.Monad ((=<<))
import Data.List     (transpose, nub, union, group, sortBy)
import Data.Function (on)

import qualified Data.DList      as DL
import qualified Data.Map        as Map

--------------------------------------------------------------------------------
--
--                                Constructs
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- |                              Definitions
--
-- * Definition 1.0
--    A step S is a triple (p, e, b) where p, the step preconditions, is a set 
--    of qunatified literals; e, the step effects, is a set of effects; and b, 
--    the the step constraints, is a set of equality constraints on free 
--    variables in p.
--
-- * Definition 1.1
--    An effect E is a triple (p, o, b) where p, the effect preconditions, is a
--    set of quantfied literals; o, the effect postconditions, is a set of
--    quantified literals; and b, the effect binding constraints, is a set of
--    equality constraints on free variables in p and o.
--
-- * Definition 1.2
--    A causal link is a quadruple (Si, e, r, Sj), denoted Si -(e,r)-> Sj, where
--    r is a (possibly negated) precondition of Sj (or a precondition of one of
--    its effects), and e is an effect of Si, and there exists an q in o(e) such
--    that q unifies with r.
--
-- * Definition 1.3
--    A plan is a quadruple (S, B, O, L), where S is a set of steps, B is a set
--    of binding constraints on free variables in S, O is a set of ordering 
--    constraints { Si < Sj | Si, Sj in S}, and L is a set of causal links.
--
-- * Definition 1.4
--    A planning problem a is a quadruple (A, T, U, I) where A is a set of 
--    action schemata, T is a set of literals indicating the initial conditions,
--    I is a set of quantified clauses indicating the goals and U is a universe
--    of discourse for variables in A, T and I.
--
-- * Definition 1.5
--    ...
--

-- | Step, by definition 1.0.
data Step = Step {
      step_id         :: ID
    , step_precond    :: [QLiteral]
    , step_effect     :: Effect
    , step_eqcons     :: [QBinding]
  }
            
instance Eq Step where
  Step {step_id = x} == Step {step_id = y} = x == y  

instance Show Step where
  show = show . step_precond

-- | Effect, by definition 1.1.
data Effect = Effect {
      effect_precond  :: [QLiteral]
    , effect_postcond :: [QLiteral]
    , effect_eqcons   :: [QBinding]
  } deriving (Eq, Show)

-- | Causal link, by definition 1.2. 
data CausalLink = Link {
      link_from       :: Step
    , link_to         :: Step
    , link_gives      :: QLiteral
  }
                  
-- | Plan, by definition 1.3. 
--   Set of open preconditions added for book-keeping.
data Plan = Plan {
      plan_steps      :: [Step]
    , plan_eqcons     :: [QBinding]
    , plan_ordering   :: [(Step, Step)]
    , plan_links      :: [CausalLink]
    , plan_open       :: [(Step, QLiteral)]
  }
            
--------------------------------------------------------------------------------
--                                                                       * Types

type ID         = String
type Value      = String
type QLiteral   = Literal ID Value
type QBinding   = Binding ID Value

type Goal       = [QLiteral]
type Start      = [QLiteral]
type Constraint = [QLiteral]
type Operators  = [Int]

--------------------------------------------------------------------------------
--                                                         ** Empty constructors
            
emptyStep = Step {
      step_id         = ""
    , step_precond    = []
    , step_effect     = emptyEffect
    , step_eqcons     = []
  }

emptyEffect = Effect {
      effect_precond  = []
    , effect_postcond = []                 
    , effect_eqcons   = []
  }
              
emptyLink = Link {
      link_from  = emptyStep
    , link_to    = emptyStep
    , link_gives = undefined
  }

emptyPlan = Plan {
      plan_steps      = []
    , plan_eqcons     = []  
    , plan_ordering   = []
    , plan_links      = []
    , plan_open       = []
  }
            
--------------------------------------------------------------------------------
--
--                                 Algorithm
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | ...
--
-- function pop(initial-state, conjunctive-goal, operators)
--     // non-deterministic algorithm
--   plan = make-initial-plan(initial-state, conjunctive-goal);
--   loop:
--     begin
--       if solution?(plan) then return plan;
--       (S-need, c) = select-subgoal(plan);
--       choose-operator(plan, operators, S-need, c);
--       resolve-threats(plan);
--     end
-- end
--
partial_order_planner :: Start -> Goal -> Operators -> Plan
partial_order_planner start goal operators = loop make_initial_plan
  where
    loop plan | solution plan = plan
              | otherwise     = loop 
                              $ resolve_threats
                              $ (uncurry $ choose_operator plan operators)
                              $ select_subgoal plan
    
    make_initial_plan = 
      let f = emptyStep { step_precond = goal }
          s = emptyStep { step_effect  = emptyEffect {effect_postcond = start} }
       in emptyPlan {
                plan_steps    = [s,f]
              , plan_ordering = [(s,f)]
              , plan_open     = zip (repeat f) goal
            }

--------------------------------------------------------------------------------
-- | ...
--
-- function solution?(plan)
--   if causal-links-establishing-all-preconditions-of-all-steps(plan)
--      and all-threats-resolved(plan)
--      and all-temporal-ordering-constraints-consistent(plan)
--      and all-variable-bindings-consistent(plan)
--   then return true;
--   else return false;
-- end
--
solution :: Plan -> Bool
solution plan 
  |    causal_links_establishing_all_preconditions_of_all_steps plan
    && all_threats_resolved plan
    && all_temporal_ordering_constraints_consistent plan
    && all_variable_bindings_consistent plan
              = True
  | otherwise = False
  where
    -- ^ Since the open precoditions is logged in the plan this is reduced to a
    --   simple null check of that log.
    causal_links_establishing_all_preconditions_of_all_steps = null . plan_open
          
    -- ^ Finding threats is done by searching for any step Ai, where Aj < Ai < Ak 
    --   is consistent, which threathen the causal link from Aj to Ak.
    all_threats_resolved plan = any (not . null) $
      [[ all_temporal_ordering_constraints_consistent $ extendOrdering x y plan
       | y <- plan_links plan, y `threatens` x] 
       | x <- plan_links plan]
                                  
    -- ^ Temportal orderings are constistent if the DAG created using the plans
    --   ordering constraints as edges contains no cycles.
    all_temporal_ordering_constraints_consistent = and . map snd . cycle . plan_ordering
    
    -- ^ Variable bindings are consisten when no step in the plans set of causal
    --   links binds a variable to different values.
    all_variable_bindings_consistent = and . map binding_consistent . plan_links
    

-- | Checks if a causal link threathens another
threatens :: CausalLink -> CausalLink -> Bool
threatens (Link {link_gives = x}) (Link {link_gives = y}) = invert x == y
        
-- | Extends the orderings of a plan with a merger of two links, enabling threath checking
extendOrdering :: CausalLink -> CausalLink -> Plan -> Plan
extendOrdering x y plan = plan { 
  plan_ordering = (link_from x, link_from y)
                : (link_from y, link_to   x)
                : plan_ordering plan       }
                          
-- | Checks if the bindings are consistent in a causal link
binding_consistent :: CausalLink -> Bool
binding_consistent (Link (Step {step_eqcons = from}) (Step {step_eqcons = to}) _) = 
  and . map (allEq . map snd) . group . sortBy (compare `on` fst) $ from ++ to
    
--------------------------------------------------------------------------------
-- | ...
--
-- function select-subgoal(plan)
--   pick a plan step S-need from steps(plan) with a precondition c
--      that has not been achieved;
--   return (S-need, c);
-- end
--
select_subgoal :: Plan -> (Step, QLiteral)
select_subgoal plan = ifNull (plan_open plan) head (error "No open steps left")

ifNull :: [a] -> ([a] -> b) -> b -> b
ifNull [] _ b = b
ifnull xs a _ = a xs

--------------------------------------------------------------------------------
-- | ...
--
-- procedure choose-operator(plan, operators, S-need, c)
--   choose a step S-add by either
--     Step Addition: adding a new step from operators that
--        has c in its Add-list
--     or Simple Establishment: picking an existing step in Steps(plan)
--        that has c in its Add-list;
--   if no such step then return fail;
--   add causal link "S-add --->c S-need" to Links(plan);
--   add temporal ordering constraint "S-add < S-need" to Orderings(plan);
--   if S-add is a newly added step then
--     begin
--     add S-add to Steps(plan);
--     add "Start < S-add" and "S-add < Finish" to Orderings(plan);
--     end
-- end
--
choose_operator :: Plan -> Operators -> Step -> QLiteral -> Plan
choose_operator plan operators s_need c
  | not . null $ step_addition        = undefined
  | not . null $ simple_establishment = undefined
  | otherwise  = error "fail" 
  where
    step_addition        = undefined
    {-
       find step which can bind an open variable to, or contains, c
    -}
    
    simple_establishment = undefined
      where steps = plan_steps plan
    {-
       list used steps
       find steps with c as "gives"
    -}
            
-- check if a quantified literal clashes with step and its effects constraints
step_bound :: Step -> QLiteral -> Bool
step_bound step lit = undefined

-- check if a quantified literal clashes with the effects constraints
effect_bound :: Effect -> QLiteral -> (QLiteral, QLiteral)
effect_bound effect lit = undefined
  where cons = effect_eqcons   effect
        post = effect_postcond effect
        
        go   = undefined 

--------------------------------------------------------------------------------
-- | ...
--
-- procedure resolve-threats(plan)
--   foreach S-threat that threatens link "Si --->c Sj" in Links(plan)
--    begin
--      choose either
--        Demotion: add "S-threat < Si" to Orderings(plan)
--        or Promotion: add "Sj < S-threat" to Orderings(plan);
--      if not(consistent(plan)) then return fail;
--    end
-- end
--    
resolve_threats :: Plan -> Plan
resolve_threats plan = undefined

--------------------------------------------------------------------------------
--                                                           ** Helper functions

invert :: QLiteral -> QLiteral
invert (Positive p) = Negative p
invert (Negative p) = Positive p

--------------------------------------------------------------------------------
--
--                                 Unit tests
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--                                                              * Sample Objects

--------------------------------------------------------------------------------
-- | Basic example of a "good" plan
--
-- Four steps:            S1, S2, S3 & S4. 
-- Temporal constraints:  (S1 < S2), (S2 < S3), (S3 < S4)
-- Causal links:          (S4 -(c)-> S3), (S3 -(not c)-> S2), (S2 -(a)-> S1)  
-- Equality constraints:  (c == a)
goodPlan = emptyPlan { plan_steps    = [s1, s2, s3, s4]
                     , plan_eqcons   = []
                     , plan_ordering = [ (s1, s2)
                                       , (s2, s3)
                                       , (s3, s4)
                                       ] 
                     , plan_links    = [ emptyLink { link_from  = s2
                                                   , link_to    = s1
                                                   , link_gives = a 
                                                   }
                                       , emptyLink { link_from  = s3
                                                   , link_to    = s2
                                                   , link_gives = invert c
                                                   }
                                       , emptyLink { link_from  = s4
                                                   , link_to    = s3 
                                                   , link_gives = c
                                                   }
                                       ]
                     }
  where
    (c , a)          = ( Positive (Predicate "P" [Variable "C"])
                       , Positive (Predicate "P" [Variable "A"])
                       )
    (s1, s2, s3, s4) = ( emptyStep { step_id      = "S1"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = [a]
                                                                , effect_postcond = [invert a]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       , emptyStep { step_id      = "S2"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = [invert c]
                                                                , effect_postcond = [a]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       , emptyStep { step_id      = "S3"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = [c]
                                                                , effect_postcond = [invert c]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       , emptyStep { step_id      = "S4"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = []
                                                                , effect_postcond = [c]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       )  

--------------------------------------------------------------------------------
-- | Basic example of a "bad" plan, used for debugging by injecting various
--   faults into the plan.
--
-- Four steps:            S1, S2, S3 & S4. 
-- Temporal constraints:  (S1 < S2), (S2 < S3), (S3 < S4)
-- Causal links:          (S4 -(c)-> S3), (S3 -(not c)-> S2), (S2 -(a)-> S1)  
-- Equality constraints:  (c == a)
badPlan = emptyPlan { plan_steps    = [s1, s2, s3, s4]
                    , plan_eqcons   = []
                    , plan_ordering = [ (s1, s2)
                                      , (s2, s1)
                                      , (s3, s4)
                                      ] 
                    , plan_links    = [ emptyLink { link_from  = s2
                                                  , link_to    = s1
                                                  , link_gives = a 
                                                  }
                                      , emptyLink { link_from  = s3
                                                  , link_to    = s2
                                                  , link_gives = invert c
                                                  }
                                      , emptyLink { link_from  = s4
                                                  , link_to    = s3 
                                                  , link_gives = c
                                                  }
                                      ]
                    }
  where
    (c , a)          = ( Positive (Predicate "P" [Variable "C"])
                       , Positive (Predicate "P" [Variable "A"])
                       )
    (s1, s2, s3, s4) = ( emptyStep { step_id      = "S1"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = [a]
                                                                , effect_postcond = [invert a]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       , emptyStep { step_id      = "S2"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = [invert c]
                                                                , effect_postcond = [a]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       , emptyStep { step_id      = "S3"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = [c]
                                                                , effect_postcond = [invert c]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       , emptyStep { step_id      = "S4"
                                   , step_precond = []
                                   , step_effect  = emptyEffect { effect_precond  = []
                                                                , effect_postcond = [c]
                                                                , effect_eqcons   = []
                                                                }
                                   , step_eqcons  = []
                                   }
                       )  

--------------------------------------------------------------------------------
--                                                                  * Test Cases



--------------------------------------------------------------------------------
--
--                                Scrap Code
--
--------------------------------------------------------------------------------

{-
    -- | A variant of insertion sort fitted to find conflicts in the
    --   set of orderings. Extended to use non-determinism for different
    --   orderings that can arise, hence checking for conflicts translates
    --   to checking if there is any result at all.
    --
    insertion_sort :: (Eq a) => [(a, a)] -> Bool
    insertion_sort xs = any (not . null) $ go xs
      where
        go ((x,y):[]) = [x, y] : []
        go (x:xs)     = concatMap (insert x) $ go xs
        
    -- | Inserts the given ordering pair into the list of orderings,
    --   if any ambiguity arises as to the ordering a list for each
    --   instance is generated. The cases considered are:
    --     - (p < q) (q < p) -> [ ]
    --     - (p < q) (p < q) -> [ p , q ]
    --     - (p < q) (p < s) -> [ p , q , s ] | [ p , s , q ]
    --     - (p < q) (q < s) -> [ p , q , s ]
    --     - (p < q) (s < p) -> [ s , p , q ]
    --     - (p < q) (s < q) -> [ s , p , q ] | [ p , s , q ]
    -- 
    insert :: (Eq a) => (a, a) -> [a] -> [[a]]
    insert _ [] = []
    insert y@(p, q) x@(r:[])
      | p == r    = (r : q : [])                         : []
      | q == r    = (p : r : [])                         : []
      | otherwise = (r : p : q : []) : (p : q : r : [])  : []
    insert y@(p,q) x@(r:s:xs)
      | y == (s,r) = []
      | y == (r,s) = x : []
      | p == r     = (p : q : s : xs) : (p : s : q : xs) : []
      | q == r     = (p : q : s : xs)                    : []
      | p == s     = (s : p : q : xs)                    : []
      | q == s     = (r : p : q : xs) : (p : r : q : xs) : []
      | otherwise  = map ((r:) . (s:)) $ insert y xs
-}

{-
  let links   = plan_links plan
      threats = [(x, y) | x <- links, y <- links, y `threatens` x]
   in or . map all_temporal_ordering_constraints_consistent $ extendedPlans plan threats
  where 
    threatens :: CausalLink -> CausalLink -> Bool
    threatens (Link {link_gives = x}) (Link {link_gives = y}) = invert x == y
    
    extendedPlans :: Plan -> [(CausalLink, CausalLink)] -> [Plan]
    extendedPlans plan = map (f plan)
      where
        f plan (x, y) = plan {plan_ordering = (link_from x, link_from y)
                                            : (link_from y, link_to x) 
                                            : plan_ordering plan }
                            -}