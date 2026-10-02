{- | The automata of this package, defined as simply as possible.

This module is the reference that the other modules are checked against. It
works on the explicit-state automata of "Data.CFTA", with a 'Constraint' on
every transition, and each operation follows its definition:

* A term is accepted at a state when a transition of the state has the
  term's symbol and arity, each child is accepted at the child state of the
  transition, and the term satisfies the constraint of the transition.
* A function from the caller decides whether a term satisfies a constraint.
  For equality constraints it is 'equalitiesOnly': the term satisfies
  'constraintAsGuard' of the constraint, where 'Same' compares the subterms
  at two paths, both paths must exist, and the connectives are Boolean. A
  refinement guard needs the refinement evaluator and a solver.
* The terms up to a depth are the accepted terms among every tree of the
  underlying graph up to that depth. A leaf has depth zero.
* 'union', 'intersect', and 'boundDepth' are the textbook constructions over
  states.

There is no sharing, no memo of results, no unification, and no reduction,
so the operations are slow: the number of trees grows exponentially with
the depth. The tests compare the other modules with this one.
-}
module Data.CFTA.Simple (
    -- * Semantics
    subtermAt,
    guardHolds,
    equalitiesOnly,
    acceptsM,
    accepts,
    termsUpToM,
    termsUpTo,

    -- * Constructions
    union,
    intersect,
    boundDepth,
) where

import Control.Monad (filterM)
import Data.Either (fromRight)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Tree (Tree (..))

import Data.CFTA (FTA, Transition (..), initialState, mkFTA, states, transitionsFrom)
import Data.CFTA.Constraint (Constraint, Guard (..), conjoinConstraints, constraintAsGuard)
import Data.CFTA.Path (Path, unPath)

-- | The subterm at a path, when the term has that path.
subtermAt :: Path -> Tree symbol -> Maybe (Tree symbol)
subtermAt path term = go (unPath path) term
  where
    go [] subterm = Just subterm
    go (index : rest) (Node _ children)
        | index >= 0, child : _ <- drop index children = go rest child
        | otherwise = Nothing

{- | Whether a complete term satisfies a guard. 'Same' compares subterms, the
connectives are Boolean, and the given function decides every other atom.
-}
guardHolds :: (Monad m, Eq symbol) => (Guard -> Tree symbol -> m Bool) -> Guard -> Tree symbol -> m Bool
guardHolds atom guard term = case guard of
    Top -> pure True
    Bottom -> pure False
    Same left right -> pure $ case (subtermAt left term, subtermAt right term) of
        (Just leftTerm, Just rightTerm) -> leftTerm == rightTerm
        _ -> False
    Not inner -> not <$> guardHolds atom inner term
    And parts -> allM (\part -> guardHolds atom part term) parts
    Or parts -> anyM (\part -> guardHolds atom part term) parts
    _ -> atom guard term

{- | Decide a constraint by 'guardHolds' of 'constraintAsGuard'. 'Nothing' when
the constraint has an atom that is not 'Same'.
-}
equalitiesOnly :: (Eq symbol) => Constraint -> Tree symbol -> Maybe Bool
equalitiesOnly constraint = guardHolds (\_ _ -> Nothing) (constraintAsGuard constraint)

-- | Whether the automaton accepts a term. The function decides whether a term satisfies a constraint.
acceptsM ::
    (Monad m, Ord state, Eq symbol) =>
    (Constraint -> Tree symbol -> m Bool) -> FTA state symbol Constraint -> Tree symbol -> m Bool
acceptsM satisfies automaton = acceptedAt (initialState automaton)
  where
    acceptedAt state term = anyM (fits term) (transitionsFrom automaton state)
    fits term@(Node symbol children) (Transition expected childStates constraint)
        | expected /= symbol || length childStates /= length children = pure False
        | otherwise =
            allM id (zipWith acceptedAt childStates children <> [satisfies constraint term])

{- | Whether an automaton whose constraints are equalities accepts a term.
'Nothing' when a constraint has an atom that is not 'Same'.
-}
accepts :: (Ord state, Eq symbol) => FTA state symbol Constraint -> Tree symbol -> Maybe Bool
accepts = acceptsM equalitiesOnly

-- | Every accepted term of depth at most the bound, in term order, each once.
termsUpToM ::
    (Monad m, Ord state, Ord symbol) =>
    (Constraint -> Tree symbol -> m Bool) -> Int -> FTA state symbol Constraint -> m [Tree symbol]
termsUpToM satisfies depth automaton = filterM (acceptsM satisfies automaton) $ Set.toList $ trees depth $ initialState automaton
  where
    -- The trees of the underlying graph at a state, of depth at most the bound, by bound.
    levels = [Map.fromList [(state, level bound state) | state <- states automaton] | bound <- [0 ..]]
    trees bound state
        | bound < 0 = Set.empty
        | otherwise = Map.findWithDefault Set.empty state (levels !! bound)
    level bound state =
        Set.fromList
            [ Node symbol children
            | Transition symbol childStates _ <- transitionsFrom automaton state
            , children <- traverse (Set.toList . trees (bound - 1)) childStates
            ]

-- | 'termsUpToM' for an automaton whose constraints are equalities.
termsUpTo :: (Ord state, Ord symbol) => Int -> FTA state symbol Constraint -> Maybe [Tree symbol]
termsUpTo = termsUpToM equalitiesOnly

-- | The terms of either automaton: a new initial state has the transitions of both initial states.
union ::
    (Ord left, Ord right, Ord symbol) =>
    FTA left symbol Constraint -> FTA right symbol Constraint -> FTA (Maybe (Either left right)) symbol Constraint
union left right =
    build Nothing $
        (Nothing, transitions Left left (initialState left) <> transitions Right right (initialState right))
            : [(Just (Left state), transitions Left left state) | state <- states left]
                <> [(Just (Right state), transitions Right right state) | state <- states right]
  where
    transitions tag automaton state =
        [ Transition symbol (map (Just . tag) children) constraint
        | Transition symbol children constraint <- transitionsFrom automaton state
        ]

{- | The terms of both automata: the product of the states. A pair of
transitions with one symbol and arity gives a transition with both
constraints.
-}
intersect ::
    (Ord left, Ord right, Ord symbol) =>
    FTA left symbol Constraint -> FTA right symbol Constraint -> FTA (left, right) symbol Constraint
intersect left right = build (initialState left, initialState right) [(pair, transitions pair) | pair <- reachable]
  where
    transitions (leftState, rightState) =
        [ Transition symbol (zip leftChildren rightChildren) (conjoinConstraints leftConstraint rightConstraint)
        | Transition symbol leftChildren leftConstraint <- transitionsFrom left leftState
        , Transition other rightChildren rightConstraint <- transitionsFrom right rightState
        , symbol == other
        , length leftChildren == length rightChildren
        ]
    reachable = Set.toList $ closure Set.empty [(initialState left, initialState right)]
    closure seen [] = seen
    closure seen (pair : pending)
        | Set.member pair seen = closure seen pending
        | otherwise = closure (Set.insert pair seen) (concatMap transitionChildren (transitions pair) <> pending)

-- | The terms of depth at most the bound: a state with the depth that its terms may still have.
boundDepth :: (Ord state, Ord symbol) => Int -> FTA state symbol Constraint -> FTA (state, Int) symbol Constraint
boundDepth bound automaton =
    build
        (initialState automaton, bound)
        [ ( (state, remaining)
          , [ Transition symbol [(child, remaining - 1) | child <- children] constraint
            | Transition symbol children constraint <- transitionsFrom automaton state
            , remaining > 0 || (remaining == 0 && null children)
            ]
          )
        | state <- states automaton
        , remaining <- [min 0 bound .. bound]
        ]

-- | Build an automaton from rows that name every state they use.
build ::
    (Ord state, Ord symbol) => state -> [(state, [Transition state symbol Constraint])] -> FTA state symbol Constraint
build initial rows =
    fromRight (error "microcfta bug in Data.CFTA.Simple: a construction built an invalid automaton") $
        mkFTA initial rows

-- | Whether some element satisfies a monadic predicate, from the left.
anyM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM predicate (x : rest) = predicate x >>= \found -> if found then pure True else anyM predicate rest

-- | Whether every element satisfies a monadic predicate, from the left.
allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM _ [] = pure True
allM predicate (x : rest) = predicate x >>= \holds -> if holds then allM predicate rest else pure False
