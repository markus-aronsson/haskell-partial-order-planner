{-#LANGUAGE GADTs, KindSignatures #-}

module FOL 
  ( 
    -- ^ Constructs
    Term (..)
  , Formula (..)
  , Literal (..)
  , Binding (..)
    
    -- ^ Run functions
  , mgu
  , disagreementSet  
    
    -- ^ General work functuins
  , allEq        -- Eq a => [a] -> Bool
  , allEqBy      -- Eq a => (a -> a -> Bool) -> [a] -> Bool
  ) where

import Control.Monad ((=<<))
import Data.List     (transpose, nub)
import Data.DList    (DList)
import Data.Map      (Map)

import qualified Data.DList as DL
import qualified Data.Map   as Map

--------------------------------------------------------------------------------
--
--                               Logic Constructs
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--                                                           * First order logic

-- | Terms 
data Term a b where
  Variable    :: a               -> Term a b
  Constant    :: b               -> Term a b
  Function    :: a -> [Term a b] -> Term a b

-- | Atmoic formulas
data Formula a b where
  Predicate   :: a -> [Term a b]  -> Formula a b

-- | Quantified literals
data Literal a b where
  Positive    :: Formula a b -> Literal a b
  Negative    :: Formula a b -> Literal a b
  
-- | Variable binding
type Binding a b = (Term a b, Term a b)
                -- (var,      term    )
  
--------------------------------------------------------------------------------
--                                                            ** Logic instances

----------------------------------------
-- Equality
--
-- Notes:
--   - Some of these are quite forced and 
--     should really be improved upon to use 
--     reflexivity and the likes instead...

instance (Eq a, Eq b) => Eq (Literal a b) where
  (Positive f) == (Positive g) = f == g
  (Negative f) == (Negative g) = f == g
  _            == _            = False

instance (Eq a, Eq b) => Eq (Formula a b) where
  (Predicate f xs) == (Predicate g ys) = f == g && xs == ys
  
instance (Eq a, Eq b) => Eq (Term a b) where
  (Variable x)    == (Variable y)    = x == y
  (Constant x)    == (Constant y)    = x == y
  (Function f xs) == (Function g ys) = f == g && xs == ys
  _               == _               = False
  
----------------------------------------
-- Ordering
  
instance (Ord a, Ord b) => Ord (Term a b) where
  (Variable x) `compare` (Variable y) = x `compare` y

----------------------------------------
-- Show

instance (Show a, Show b) => Show (Formula a b) where
  show (Predicate f xs) = "pred " ++ show f ++ " (" ++ show xs ++ ")"

instance (Show a, Show b) => Show (Term a b) where
  show (Variable x)    = "var "   ++ show x
  show (Constant x)    = "const " ++ show x
  show (Function f xs) = "fun "   ++ show f ++ " (" ++ show xs ++ ")"
  
instance (Show a, Show b) => Show (Literal a b) where
  show (Positive x) = "Positive " ++ show x
  show (Negative x) = "Negative " ++ show x

--------------------------------------------------------------------------------
--
--                            Auxilirary Functions
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--                                                        * Most general unifier

-- | Finds the most general unifier of the set of terms, Nothing is returned
--   if no such unifier exists.  There is a simple algorithm for finding the 
--   most general unifier of a set of expressions. First, we need to define the 
--   disagreement set of a set of expressions. This is found by (textually) 
--   finding the first symbol starting from the left that is not the same in 
--   every expression and extracting the subexpressions that begin with that 
--   symbol at that position in each expression of the set. The resulting set 
--   of subexpressions is the disagreement set. For example, the disagreement 
--   set for [ P(x,y,a), P(x,f(g),b), P(x,f(g),x) ] is [ (y, f(g)) ]. 
mgu :: (Eq a, Eq b) => 
          [Formula a b]       -- ^ Predicates 
       -> Maybe [Binding a b] -- ^ Bindings
mgu preds = loop preds []
  where
    loop preds substs 
      | singleton preds = Just substs
      | otherwise       = maybe Nothing 
          (\(t,s) -> if null t then Just s else loop t s)
          (disagreementSet preds substs)

    singleton :: (Eq a, Eq b) => [Formula a b] -> Bool
    singleton = allEq

-- | Finds the first disagreement set in a set of terms, bound by the specified
--   initial bindings. If such a disagreement set exists, the most general 
--   unification is found and the terms are substituted accordingly to the 
--   unifier, which is then added to the set of bindings. In the case where no 
--   unification is neccessary an empty set of terms is returned. However, 
--   if no such unifier exists Nothing is returned instead. The disagreement 
--   set is found by lexographically traversing the terms left to right, and 
--   picking the first conflicting set of terms found.
disagreementSet :: (Eq a, Eq b) => 
                       [Formula a b]       -- ^ Set of predicates
                    -> [Binding a b]       -- ^ Set of initial bindings
                    -> Maybe               -- ^ Possibly formed disagreement of
                         ( [Formula a b]   -- ^^ New predicates
                         , [Binding a b]   -- ^^ New bindings
                         )
disagreementSet predicates substitutions
  | allEq predicates = Just ([], substitutions)
  | otherwise        =
    let (names, arguments) = fmap transpose $ seperate_predicates predicates
    in if not $ allEq names
      then Nothing
      else Just . apFst (zipWith (Predicate) names)
             =<< find_disagreement arguments substitutions DL.empty
  where
    find_disagreement (t:ts) s a = case valid_set t s of
      Nothing          -> Nothing
      Just (b, t', s') -> if b then Just (transpose $ DL.toList a ++ t':ts, s')
                               else find_disagreement ts s' (DL.cons t' a)

    valid_set ts s
      | allEq ts               = Just (False, ts, s)
      | impossible_unification = Nothing
      | conflicting_functions  = function_search
      | otherwise              = 
        let s'@(v, t) = ( head vars
                        , head $ if null cons && null funs
                                   then tail vars
                                   else cons ++ funs
                        )
          in if contains_variable v t
            then Nothing
            else Just ( True
                      , substitute s' ts
                      , update_substitutions s' s
                      )
      where
        (vars, cons, funs)     = seperate_terms ts
        impossible_unification = (not $ null cons || null funs) || (not $ allEq cons)
        conflicting_functions  = (not $ allEq ts) && (null vars && null cons)
        function_search        =  
          let a = transpose $ [t | (Function _ t) <- funs]
          in case find_disagreement a s DL.empty of
            Nothing       -> Nothing
            Just (a', s') -> Just ( True
                                  , zipWith (\(Function f _) a -> Function f a) funs
                                    $ transpose a'
                                  , s'
                                  )
    
--------------------------------------------------------------------------------
            

            
            
            
            
mgu' :: (Eq a, Eq b) => [Formula a b] -> Maybe [Binding a b]
mgu' predicates = go predicates [] 
  where
    go :: (Eq a, Eq b) => [Formula a b] -> [Binding a b] -> Maybe [Binding a b]
    go ps ss  | null ps   = Just ss
              | otherwise = disagreement_set' ps ss >>= uncurry go



disagreement_set' :: (Eq a, Eq b) => 
                         [Formula a b]       -- ^ Set of predicates
                      -> [Binding a b]       -- ^ Set of initial bindings
                      -> Maybe               -- ^ Possibly formed disagreement of
                           ( [Formula a b]   -- ^^ Substituted predicates
                           , [Binding a b]   -- ^^ Introduced bindings
                           )
disagreement_set' ps ss | allEq ps = Just ([], ss)
disagreement_set' ps ss 
  | not $ allEq names = Nothing
  | otherwise         = Just .
      apFst (zipWith (Predicate) names) =<< disagreement' terms ss DL.empty
  where
    (names, terms) = fmap transpose . unzip $ [(a, b) | (Predicate a b) <- ps]

disagreement' :: (Eq a, Eq b) => 
                    [[Term a b]] 
                 -> [Binding a b] 
                 -> DList a 
                 -> Maybe 
                      ( [[Term a b]]
                      , [Binding a b]
                      )
disagreement' = undefined



--------------------------------------------------------------------------------
--
--                     Franz Baader & Wayne Snyder Unification
--
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- |                              Definitions
--
-- * Definition 2.11
--   A term relation is an equivalence relation on terms, and is homogeneous if
--   no term is equivalent to a proper subterm of itself. A unification relation
--   is a homogeneous, acyclic term relation satisfying the unification axiom:
--     For any f and terms si and ti
--       f(s1, ..., sn) ~= f(t1, ..., tn) -> s1 ~= t1 & ... & sn ~= tn
--   The unification closure of s and t, when it exists, is the least
--   unification relation which makes s and t equivalent.
--
-- * Definition 2.23
--   For any term relation ~=, let a schema function be a function s (sigma),
--   from equivalence classes to terms such that for any class C,
--     i)  s(C) belongs to C; and
--     ii) s(C) is a variable only if C consists entirely of variables.
--   The term s(C) will be called the schema term for C.
--
-- * Definition 2.14
--   For any unification closure ~=, define o~= by:
--         
--     x o~= = { y                      if s([x]) = y
--             { f(s1 o~=, ..., sn o~=) if s([x]) = f(s1, ..., sn)


--------------------------------------------------------------------------------
--
--                                 Algorithm
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | ...
--
-- function unify(s : node, t : node)
--   begin
--     unify_closure(s, t);
--     find_solution(s);
--   end;
--

--------------------------------------------------------------------------------
-- | ...
--
--





































--------------------------------------------------------------------------------
--                                                           ** Helper functions
            
-- | Searches a term for a variable, returns True if the terms 
--   containts that variable, false otherewise.
contains_variable :: (Eq a, Eq b) => Term a b -> Term a b -> Bool
contains_variable var term = case term of
  Variable _ | var == term -> True
             | otherwise   -> False
  Constant _               -> False
  Function _ args          -> any (contains_variable var) args
    
-- | Seperates the name and arguments of predicates into a pair their sets.
seperate_predicates :: (Eq a, Eq b) => [Formula a b] -> ([a], [[Term a b]])
seperate_predicates forms = unzip $ [(a, b) | (Predicate a b) <- forms]
                              
-- | Seperates the different kinds of terns in a list into a tuple.
seperate_terms :: (Eq a, Eq b) => [Term a b] -> ([Term a b], [Term a b], [Term a b])
seperate_terms terms = go terms [] [] []
  where go []     vars cons funs = (vars, cons, funs)
        go (x:xs) vars cons funs = 
          uncurry3 (go xs) $ case x of
            Variable {} -> ((x:vars), cons,     funs)
            Constant {} -> (vars,     (x:cons), funs)
            Function {} -> (vars,     cons,     (x:funs))
                
-- | Subsititutes the first occurence of a free variabel to that 
--   specefied in the binding with the matching term.
substitute :: (Eq a, Eq b) => Binding a b -> [Term a b] -> [Term a b]
substitute _             []        = []
substitute s@(var, term) (t:terms)
  | contains_variable var t = update_term s t : substitute s terms
  | otherwise               = t : substitute s terms

-- | Updates a set of bindings to include a new binding
update_substitutions :: (Eq a, Eq b) => Binding a b -> [Binding a b] -> [Binding a b]
update_substitutions s substs = s : map (update_binding s) substs
  where
    update_binding :: (Eq a, Eq b) => Binding a b -> Binding a b -> Binding a b
    update_binding p@(var, term) q@(var', term')
      | contains_variable var term' = fmap (update_term p) q
      | otherwise                   = q
    
-- | Updates a term by the application of an binding
update_term :: (Eq a, Eq b) => Binding a b -> Term a b -> Term a b
update_term p@(var, term) old_term = case old_term of
  (Variable _) | old_term == var -> term
  (Constant _)                   -> old_term
  (Function f args)              -> Function f $ map (update_term p) args

--------------------------------------------------------------------------------
--                                                    * General helper functions

allEq                :: Eq a => [a] -> Bool
allEq                = allEqBy (==)

allEqBy              :: Eq a => (a -> a -> Bool) -> [a] -> Bool
allEqBy f xs         = all (f $ head xs) xs

curry3               :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 f x y z       = f (x, y, z) 

uncurry3             :: (a -> b -> c -> d) -> ((a, b, c) -> d)
uncurry3 f (a, b, c) = f a b c

apFst                :: (a -> c) -> (a, b) -> (c, b)
apFst f (a, b)       = (f a, b)

flipP                :: (a, b) -> (b, a)
flipP (a, b)         = (b, a)
