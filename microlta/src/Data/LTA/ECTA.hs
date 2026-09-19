{-# LANGUAGE NamedFieldPuns #-}

{- | A semantics-preserving optimization from reduced LTAs to MicroECTA.

The source remains an LTA. This module accepts only the fragment whose guards
have already been lowered to positive 'EqConstraints'. It then reuses
MicroECTA's equality-aware representation and enumeration without teaching the
LTA semantics about generator joins.

The conversion accepts acyclic automata only. Bound a recursive LTA before
conversion; 'RecursiveEqualityState' reports one that was not.
-}
module Data.LTA.ECTA (
    EqualityView,
    EqualityViewError (..),
    toECTA,
    equalityRoot,
    decodeTerm,
) where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Tree as Tree

import qualified Data.CFTA as FTA
import qualified Data.CFTA.Equality as ECTA
import Data.CFTA.Equality.Constraints (EqConstraints)
import qualified Data.CFTA.Interned as Common
import Data.LTA (
    EqualityAutomaton,
    LiquidSymbol,
    State,
    automatonTransitions,
 )

-- | A MicroECTA root plus the finite alphabet needed to decode its terms.
data EqualityView = EqualityView
    { equalityRoot :: !(ECTA.Node Int EqConstraints)
    -- ^ The converted automaton over the integer alphabet.
    , equalityAlphabet :: !(IntMap.IntMap LiquidSymbol)
    -- ^ The liquid symbol behind each integer label.
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
toECTA automaton = do
    -- The alphabet map is injective, so renaming cannot change an arity.
    graph <- case FTA.mapSymbols (alphabet Map.!) automaton of
        Left _ -> error "microlta bug in Data.LTA.ECTA.toECTA: an injective renaming changed a validated arity"
        Right renamed -> Right renamed
    root <- case Common.fromFTA graph of
        Left (Common.RecursiveFTAState state) -> Left $ RecursiveEqualityState state
        Right node -> Right node
    pure $ EqualityView root (IntMap.fromList [(identifier, symbol) | (symbol, identifier) <- Map.toList alphabet])
  where
    alphabet =
        Map.fromList $
            zip
                ( Set.toAscList $
                    Set.fromList
                        [FTA.transitionSymbol transition | transitions <- Map.elems $ automatonTransitions automaton, transition <- transitions]
                )
                [0 ..]

-- | Decode one term enumerated from an 'EqualityView'.
decodeTerm :: EqualityView -> Tree.Tree Int -> Either EqualityViewError (Tree.Tree LiquidSymbol)
decodeTerm EqualityView{equalityAlphabet} = Tree.foldTree decode
  where
    decode identifier children = do
        label <-
            maybe
                (Left $ UnknownEqualityLabel identifier)
                Right
                (IntMap.lookup identifier equalityAlphabet)
        Tree.Node label <$> sequence children
