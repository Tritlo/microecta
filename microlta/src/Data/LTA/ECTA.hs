{-# LANGUAGE NamedFieldPuns #-}

{- | A semantics-preserving optimization from reduced LTAs to MicroECTA.

The source remains an LTA. This module accepts only the fragment whose guards
have already been lowered to positive 'EqConstraints'. It then reuses
MicroECTA's equality-aware representation and enumeration without teaching the
LTA semantics about generator joins.

The first bridge is deliberately acyclic. Recursive LTAs remain valid, but must
be bounded before conversion until a general finite-state-to-@Mu@ conversion is
available.
-}
module Data.LTA.ECTA (
    EqualityView,
    EqualityViewError (..),
    toECTA,
    equalityRoot,
    decodeTerm,
) where

import qualified Control.Monad.State.Strict as State
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Data.ECTA as ECTA
import Data.ECTA.Term (Term (Term))
import Data.LTA (
    EqualityAutomaton,
    LiquidSymbol (LiquidSymbol),
    LiquidTerm (LiquidTerm),
    State,
    automatonInitial,
    automatonTransitions,
 )
import qualified Data.Tree.FTA as FTA

-- | A MicroECTA root plus the finite alphabet needed to decode its terms.
data EqualityView = EqualityView
    { equalityRoot :: !(ECTA.Node Int)
    , equalityAlphabet :: !(IntMap.IntMap LiquidSymbol)
    }

-- | A structural failure while converting or decoding an ECTA optimization.
data EqualityViewError
    = -- | General mutually recursive FTA conversion is not implemented yet.
      RecursiveEqualityState !State
    | -- | An ECTA term contains a label absent from its conversion alphabet.
      UnknownEqualityLabel !Int
    deriving (Eq, Show)

{- | Convert one finite acyclic equality automaton to a shared MicroECTA.

Identical complete LTA labels receive the same integer alphabet symbol. ECTA
therefore implements exactly the source automaton's syntactic equality rather
than comparing only constructor names or refinement projections.
-}
toECTA :: EqualityAutomaton -> Either EqualityViewError EqualityView
toECTA automaton =
    case Set.lookupMin $ FTA.cyclicStates automaton of
        Just state -> Left $ RecursiveEqualityState state
        Nothing ->
            Right $
                EqualityView
                    { equalityRoot = State.evalState (buildState $ automatonInitial automaton) Map.empty
                    , equalityAlphabet = IntMap.fromList [(identifier, symbol) | (symbol, identifier) <- Map.toList alphabet]
                    }
  where
    table = automatonTransitions automaton
    alphabet =
        Map.fromList $
            zip
                (Set.toAscList $ Set.fromList [FTA.transitionSymbol transition | transitions <- Map.elems table, transition <- transitions])
                [0 ..]

    buildState :: State -> State.State (Map.Map State (ECTA.Node Int)) (ECTA.Node Int)
    buildState state = do
        built <- State.get
        case Map.lookup state built of
            Just node -> pure node
            Nothing -> do
                edges <- traverse buildTransition $ Map.findWithDefault [] state table
                let node = case edges of
                        [] -> ECTA.EmptyNode
                        _ -> ECTA.Node edges
                State.modify' $ Map.insert state node
                pure node

    buildTransition transition = do
        children <- traverse buildState $ FTA.transitionChildren transition
        let symbol = FTA.transitionSymbol transition
            identifier = alphabet Map.! symbol
        pure $
            ECTA.mkEdge
                identifier
                children
                (FTA.transitionGuard transition)

-- | Decode one term enumerated from an 'EqualityView'.
decodeTerm :: EqualityView -> Term Int -> Either EqualityViewError LiquidTerm
decodeTerm EqualityView{equalityAlphabet} = go
  where
    go (Term identifier children) = do
        LiquidSymbol symbol refinement <-
            maybe
                (Left $ UnknownEqualityLabel identifier)
                Right
                (IntMap.lookup identifier equalityAlphabet)
        LiquidTerm symbol refinement <$> traverse go children
