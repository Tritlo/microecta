{- | ECTA specializations of the common interned automaton representation.

This module is exposed for downstream code that needs the representation. Its
exports are not covered by the PVP contract of the package. The wrappers check
at run time whether the symbol is the interned 'Symbol' and call the shared
engine at that concrete type; both branches compute the same value, and the
split exists so GHC specializes the engine for the common alphabet.
-}
module Data.ECTA.Internal.ECTA.Type (
    RecNodeId (..),
    Edge (ECTAEdge, InternedEdge, Edge),
    edgeId,
    uninternedEdge,
    UninternedEdge,
    uEdgeSymbol,
    uEdgeChildren,
    uEdgeEcs,
    mkEdge,
    emptyEdge,
    edgeChildren,
    edgeEcs,
    edgeSymbol,
    setChildren,
    Node (ECTANode, InternedNode, EmptyNode, InternedMu, Rec, Node, Mu),
    InternedNode,
    internedNodeId,
    internedNodeEdges,
    internedNodeNumNestedMu,
    internedNodeFree,
    InternedMu,
    internedMuId,
    internedMuBody,
    internedMuShape,
    internedMuDepthShape,
    UninternedNode,
    IntersectId,
    pattern IntersectId,
    nodeIdentity,
    numNestedMu,
    substFree,
    freeVars,
    modifyNode,
    createMu,
    createMuDontCleanup,
    shape,
    matchMu,
    toInterned,
    fromInterned,
) where

import Data.Coerce (coerce)
import Data.Hashable (Hashable)
import Data.Set (Set)
import Data.Type.Equality ((:~~:) (HRefl))
import Data.Typeable (Typeable)
import Type.Reflection (eqTypeRep, typeRep)

import qualified Data.CFTA.Constraint as CommonConstraint
import Data.CFTA.Interned.Type (IntersectId, RecNodeId (..), pattern IntersectId)
import qualified Data.CFTA.Interned.Type as Common
import Data.CFTA.Symbol (Symbol)
import Data.ECTA.Internal.Paths (EqConstraints)

-- | Equality-constrained specialization. The wrapper has no runtime cost.
newtype Node symbol = ECTANode (Common.Node symbol EqConstraints)
    deriving (Eq, Ord, Hashable)

-- | Equality-constrained edge. The wrapper has no runtime cost.
newtype Edge symbol = ECTAEdge (Common.Edge symbol EqConstraints)
    deriving (Eq, Ord, Hashable)

instance (Show symbol) => Show (Node symbol) where
    showsPrec precedence (ECTANode node) = showsPrec precedence node

instance (Show symbol) => Show (Edge symbol) where
    showsPrec precedence (ECTAEdge edge) = showsPrec precedence edge

-- | Shared interned non-recursive payload.
type InternedNode symbol = Common.InternedNode symbol EqConstraints

-- | Shared interned recursive payload.
type InternedMu symbol = Common.InternedMu symbol EqConstraints

-- | Shared node input before interning.
type UninternedNode symbol = Common.UninternedNode symbol EqConstraints

-- | Shared edge input before interning.
type UninternedEdge symbol = Common.UninternedEdge symbol EqConstraints

-- | Match an interned non-recursive node.
pattern InternedNode :: InternedNode symbol -> Node symbol
pattern InternedNode payload = ECTANode (Common.InternedNode payload)

-- | The empty language.
pattern EmptyNode :: Node symbol
pattern EmptyNode = ECTANode Common.EmptyNode

-- | Match an interned recursive node.
pattern InternedMu :: InternedMu symbol -> Node symbol
pattern InternedMu payload = ECTANode (Common.InternedMu payload)

-- | A reference to a recursive binder.
pattern Rec :: RecNodeId -> Node symbol
pattern Rec ident = ECTANode (Common.Rec ident)

-- | Match an interned edge and its canonical identity.
pattern InternedEdge :: Int -> UninternedEdge symbol -> Edge symbol
pattern InternedEdge ident payload = ECTAEdge (Common.InternedEdge ident payload)

-- | Construct or inspect one unconstrained edge.
pattern Edge :: (Hashable symbol, Typeable symbol) => symbol -> [Node symbol] -> Edge symbol
pattern Edge symbol children <- ECTAEdge (Common.InternedEdge _ (Common.UninternedEdge symbol (coerce -> children) _))
  where
    Edge symbol children = mkEdge symbol children (CommonConstraint.noConstraint)

-- | Construct or inspect a set of alternatives.
pattern Node :: (Typeable symbol) => [Edge symbol] -> Node symbol
pattern Node edges <- ECTANode (Common.InternedNode (Common.MkInternedNode _ (coerce -> edges) _ _))
  where
    Node edges = mkNode edges

-- | Construct or inspect a recursive binder.
pattern Mu :: (Hashable symbol, Typeable symbol) => (Node symbol -> Node symbol) -> Node symbol
pattern Mu body <- (matchMu -> Just body)
  where
    Mu = createMu

{-# COMPLETE InternedNode, EmptyNode, InternedMu, Rec #-}
{-# COMPLETE Node, EmptyNode, Mu, Rec #-}
{-# COMPLETE InternedEdge #-}
{-# COMPLETE Edge #-}

-- | Build a canonical equality-constrained node.
mkNode :: forall symbol. (Typeable symbol) => [Edge symbol] -> Node symbol
mkNode = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.mkNode @Symbol @EqConstraints)
    Nothing -> coerce (Common.mkNode @symbol @EqConstraints)

-- | Expose the common representation without allocation.
toInterned :: Node symbol -> Common.Node symbol EqConstraints
toInterned = coerce

-- | Use an equality-constrained common node as an ECTA.
fromInterned :: Common.Node symbol EqConstraints -> Node symbol
fromInterned = coerce

-- | Build an edge with path equalities.
mkEdge :: forall symbol. (Hashable symbol, Typeable symbol) => symbol -> [Node symbol] -> EqConstraints -> Edge symbol
mkEdge = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.mkEdge @Symbol @EqConstraints)
    Nothing -> coerce (Common.mkEdge @symbol @EqConstraints)

-- | Build an edge whose child language is empty.
emptyEdge :: forall symbol. (Hashable symbol, Typeable symbol) => symbol -> Edge symbol
emptyEdge = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.emptyEdge @Symbol @EqConstraints)
    Nothing -> coerce (Common.emptyEdge @symbol @EqConstraints)

-- | Read the canonical edge identity.
edgeId :: forall symbol. Edge symbol -> Int
edgeId = coerce (Common.edgeId @symbol @EqConstraints)

-- | Read the shared edge payload.
uninternedEdge :: forall symbol. Edge symbol -> UninternedEdge symbol
uninternedEdge = coerce (Common.uninternedEdge @symbol @EqConstraints)

-- | Read the constructor label.
edgeSymbol :: forall symbol. Edge symbol -> symbol
edgeSymbol = coerce (Common.edgeSymbol @symbol @EqConstraints)

-- | Read child nodes without copying their list.
edgeChildren :: forall symbol. Edge symbol -> [Node symbol]
edgeChildren = coerce (Common.edgeChildren @symbol @EqConstraints)

-- | Read the path equalities.
edgeEcs :: forall symbol. Edge symbol -> EqConstraints
edgeEcs = coerce (Common.edgeConstraint @symbol @EqConstraints)

-- | Read the label in an edge payload.
uEdgeSymbol :: forall symbol. UninternedEdge symbol -> symbol
uEdgeSymbol = coerce (Common.uEdgeSymbol @symbol @EqConstraints)

-- | Read the children in an edge payload.
uEdgeChildren :: forall symbol. UninternedEdge symbol -> [Node symbol]
uEdgeChildren = coerce (Common.uEdgeChildren @symbol @EqConstraints)

-- | Read the equalities in an edge payload.
uEdgeEcs :: forall symbol. UninternedEdge symbol -> EqConstraints
uEdgeEcs = coerce (Common.uEdgeConstraint @symbol @EqConstraints)

-- | Replace children and retain the edge constraint.
setChildren :: forall symbol. (Hashable symbol, Typeable symbol) => Edge symbol -> [Node symbol] -> Edge symbol
setChildren = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.setChildren @Symbol @EqConstraints)
    Nothing -> coerce (Common.setChildren @symbol @EqConstraints)

-- | Read a non-empty node identity.
nodeIdentity :: forall symbol. Node symbol -> Int
nodeIdentity = coerce (Common.nodeIdentity @symbol @EqConstraints)

-- | Read the cached recursive nesting depth.
numNestedMu :: forall symbol. Node symbol -> Int
numNestedMu = coerce (Common.numNestedMu @symbol @EqConstraints)

-- | Read the cached free recursive variables.
freeVars :: forall symbol. Node symbol -> Set RecNodeId
freeVars = coerce (Common.freeVars @symbol @EqConstraints)

-- | Edit alternatives and retain an unchanged node.
modifyNode :: forall symbol. (Typeable symbol) => Node symbol -> ([Edge symbol] -> [Edge symbol]) -> Node symbol
modifyNode = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.modifyNode @Symbol @EqConstraints)
    Nothing -> coerce (Common.modifyNode @symbol @EqConstraints)

-- | Intern a recursive binder and remove a redundant binder.
createMu :: forall symbol. (Typeable symbol) => (Node symbol -> Node symbol) -> Node symbol
createMu = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.createMu @Symbol @EqConstraints)
    Nothing -> coerce (Common.createMu @symbol @EqConstraints)

-- | Intern a recursive binder without removing it.
createMuDontCleanup :: forall symbol. (Typeable symbol) => (Node symbol -> Node symbol) -> Node symbol
createMuDontCleanup = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.createMuDontCleanup @Symbol @EqConstraints)
    Nothing -> coerce (Common.createMuDontCleanup @symbol @EqConstraints)

-- | Compute the canonical recursive shape.
shape :: forall symbol. (RecNodeId -> Node symbol) -> Node symbol
shape = coerce (Common.shape @symbol @EqConstraints)

-- | Inspect a recursive binder through its substitution function.
matchMu :: forall symbol. (Hashable symbol, Typeable symbol) => Node symbol -> Maybe (Node symbol -> Node symbol)
matchMu = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.matchMu @Symbol @EqConstraints)
    Nothing -> coerce (Common.matchMu @symbol @EqConstraints)

-- | Substitute one free recursive variable.
substFree :: forall symbol. (Hashable symbol, Typeable symbol) => RecNodeId -> Node symbol -> Node symbol -> Node symbol
substFree = case eqTypeRep (typeRep @symbol) (typeRep @Symbol) of
    Just HRefl -> coerce (Common.substFree @Symbol @EqConstraints)
    Nothing -> coerce (Common.substFree @symbol @EqConstraints)

-- | Read a non-recursive payload identity.
internedNodeId :: forall symbol. InternedNode symbol -> Int
internedNodeId = coerce (Common.internedNodeId @symbol @EqConstraints)

-- | Read a non-recursive payload edge list.
internedNodeEdges :: forall symbol. InternedNode symbol -> [Edge symbol]
internedNodeEdges = coerce (Common.internedNodeEdges @symbol @EqConstraints)

-- | Read the cached nesting depth.
internedNodeNumNestedMu :: forall symbol. InternedNode symbol -> Int
internedNodeNumNestedMu = coerce (Common.internedNodeNumNestedMu @symbol @EqConstraints)

-- | Read cached free variables.
internedNodeFree :: forall symbol. InternedNode symbol -> Set RecNodeId
internedNodeFree = coerce (Common.internedNodeFree @symbol @EqConstraints)

-- | Read a recursive payload identity.
internedMuId :: forall symbol. InternedMu symbol -> Int
internedMuId = coerce (Common.internedMuId @symbol @EqConstraints)

-- | Read the recursive body.
internedMuBody :: forall symbol. InternedMu symbol -> Node symbol
internedMuBody = coerce (Common.internedMuBody @symbol @EqConstraints)

-- | Read the canonical recursive shape.
internedMuShape :: forall symbol. InternedMu symbol -> Node symbol
internedMuShape = coerce (Common.internedMuShape @symbol @EqConstraints)

-- | Read the stored recursive depth probe.
internedMuDepthShape :: forall symbol. InternedMu symbol -> Node symbol
internedMuDepthShape = coerce (Common.internedMuDepthShape @symbol @EqConstraints)
