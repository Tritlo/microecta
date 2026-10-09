{- | The private support nodes the generator engine builds.

The engine labels an open child layer with private labels. The labelling
functions replace the scaffolding of an applicative spine with one domain
constructor when @node@ closes the layer. An n-way join term keeps its private
children, and a two-way join term is wrapped and not closed. A term read back
from a generator can therefore still hold private labels.
-}
module Data.CFTA.Gen.Internal.Support (
    unconstrainedEdge,

    -- * Support nodes
    relabel,
    keyNode,
    singletonNode,
    joinNode,
    joinNodeWith,
    restrictToKey,
    restrictToKeyWith,
    familyNode,
    familyNodeWith,

    -- * Closing a layer
    labelSupport,
    labelSupportWith,
    labelTerm,
    labelTermWith,
    labelledChildren,
    spineChildren,
) where

import qualified Control.Monad.State.Strict as State
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import Data.List (compareLength)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Sequence
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Constraint (
    equalities,
    equalityConstraint,
    residual,
 )
import Data.CFTA.Equality (
    Edge (Edge),
    Node (Mu, Node),
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    mkEdge,
    unfoldOuterRec,
 )
import qualified Data.CFTA.Equality as Core
import Data.CFTA.Equality.Constraint (EqConstraints (EmptyConstraints), mkEqConstraints)
import Data.CFTA.Gen.Label (ComponentIndex, GroupIndex, KeyIndex, Label (..))
import Data.CFTA.Index (ArgumentIndex (..))
import Data.CFTA.Path (ChildIndex (..), path)

{- | Whether an edge carries no constraint at all: no path equality and no
residual obligation. Such an edge is an ordinary transition of any theory.
-}
unconstrainedEdge :: Edge symbol -> Bool
unconstrainedEdge edge = equalities (edgeConstraint edge) == EmptyConstraints && not (residual (edgeConstraint edge))

-- | Copy a graph under new symbols, keeping its constraints and bound references.
relabel ::
    (Hashable other, Typeable other) =>
    (symbol -> other) -> Node symbol -> Node other
relabel rename root = State.evalState (visit Map.empty root) Map.empty
  where
    visit environment node = do
        memo <- State.get
        case Map.lookup node memo of
            Just copied -> pure copied
            Nothing -> do
                copied <- case node of
                    Core.EmptyNode -> pure Core.EmptyNode
                    Core.Rec ident -> pure $ Map.findWithDefault (Core.Rec ident) ident environment
                    Core.InternedMu binder ->
                        pure $ Core.createMu $ \self ->
                            State.evalState
                                ( visit
                                    (Map.insert (Core.RecInt $ Core.internedMuId binder) self environment)
                                    (Core.internedMuBody binder)
                                )
                                Map.empty
                    Core.InternedNode payload -> Node <$> traverse (copyEdge environment) (Core.internedNodeEdges payload)
                State.modify' $ Map.insert node copied
                pure copied
    copyEdge environment edge = do
        children <- traverse (visit environment) $ edgeChildren edge
        pure $ mkEdge (rename $ edgeSymbol edge) children $ edgeConstraint edge

-- | Singleton key node labelling one matched group.
keyNode :: (Hashable symbol, Typeable symbol) => GroupIndex -> Node (Label symbol)
keyNode index = Node [Edge (Group index) []]

-- | The node accepting exactly one term.
singletonNode :: (Hashable symbol, Typeable symbol) => Tree.Tree symbol -> Node symbol
singletonNode = Tree.foldTree $ \symbol children -> Node [Edge symbol children]

-- TODO: The operation is the first child of the centre, before the keys, so
-- that readers match @operation : keys@ and builders cons. Alternatives,
-- measured on rank-of-term over n-way joins (JoinRankProbe, 2026-10-09)
-- against the keys before the operation read with 'unsnoc': a Seq view of the
-- centre, 1.35% fewer instructions; the keys as a Seq throughout, with
-- Seq.mapWithIndex in joinKeysMatch, 2.2% more; this order, 7.2% fewer. In
-- wall-clock this order changed join rank-of-term by -21% to +1%, within a
-- noise of 10% to 24%.

{- | One joined edge: the operation group, one group per argument, and one
equality constraint per argument tying each argument to the operation's key
at that position.
-}
joinNode ::
    (Hashable symbol, Typeable symbol) =>
    ComponentIndex -> Node (Label symbol) -> [Node (Label symbol)] -> Node (Label symbol)
joinNode = joinNodeWith id

-- | Build a joined support with a caller-supplied representation of private labels.
joinNodeWith ::
    (Hashable other, Typeable other) =>
    (Label symbol -> other) ->
    ComponentIndex ->
    Node other ->
    [Node other] ->
    Node other
joinNodeWith inject componentIndex operationSupport argumentSupports =
    Node
        [ mkEdge
            (inject JoinN)
            (operationNode : argumentNodes)
            ( equalityConstraint $
                mkEqConstraints
                    [ [path [0, argumentChild position], path [argumentChild position, 0]]
                    | position <- positions
                    ]
            )
        ]
  where
    positions = map ArgumentIndex [0 .. length argumentSupports - 1]
    -- The centre is child 0 of the joined edge, and the operation is child 0
    -- of the centre. In both edges, argument i is child i + 1.
    argumentChild (ArgumentIndex position) = ChildIndex (position + 1)
    keyNodes =
        [ singletonNode $ Tree.Node (inject $ ArgKey componentIndex position) []
        | position <- positions
        ]
    operationNode =
        Node [Edge (inject CenterKeyed) (operationSupport : keyNodes)]
    argumentNodes =
        [ Node [Edge (inject ArgKeyed) [argKeyNode, argumentSupport]]
        | (argKeyNode, argumentSupport) <- zip keyNodes argumentSupports
        ]

{- | Restrict a recursive family to one key.

A recursive family is one @Mu@ whose edges carry their key as a first child,
so an occurrence at one key is the family under an edge holding that key's
label, with a constraint equating the two. The discrimination is the
automaton's own, which is what lets the whole family share one binder.
-}
restrictToKey ::
    (Hashable symbol, Typeable symbol) =>
    KeyIndex -> Node (Label symbol) -> Node (Label symbol)
restrictToKey = restrictToKeyWith id

-- | Restrict a recursive family with a caller-supplied representation of private labels.
restrictToKeyWith ::
    (Hashable other, Typeable other) =>
    (Label symbol -> other) -> KeyIndex -> Node other -> Node other
restrictToKeyWith inject position family =
    Node
        [ mkEdge
            (inject AtKey)
            [singletonNode $ Tree.Node (inject $ Key position) [], family]
            (equalityConstraint $ mkEqConstraints [[path [0], path [1, 0]]])
        ]

{- | One recursive family node: one key-labelled edge per key.

'Node' sorts its edges by edge identity, so the edges are in interning order,
not in key order. Only drawings show this order: ranks, counts, and terms find
an edge by its key.
-}
familyNode ::
    (Hashable symbol, Typeable symbol) =>
    [(KeyIndex, Node (Label symbol))] -> Node (Label symbol)
familyNode = familyNodeWith id

-- | Build a recursive family with a caller-supplied representation of private labels.
familyNodeWith ::
    (Hashable other, Typeable other) =>
    (Label symbol -> other) -> [(KeyIndex, Node other)] -> Node other
familyNodeWith inject keyed =
    Node
        [ Edge (inject Family) [singletonNode $ Tree.Node (inject $ Key position) [], body]
        | (position, body) <- keyed
        ]

-- | Close one private support root while preserving its constraints.
labelSupport ::
    (Hashable symbol, Typeable symbol) =>
    symbol -> Node (Label symbol) -> Node (Label symbol)
labelSupport symbol = labelSupportWith id (Label symbol)

-- | Close a support layer by recognizing the private labels under a representation.
labelSupportWith ::
    (Hashable other, Typeable other) =>
    (other -> Label symbol) -> other -> Node other -> Node other
labelSupportWith original symbol support@(Node edges)
    | not (null edges)
    , all (isChoiceEdge original) edges =
        Node
            [ labelled
            | edge <- edges
            , child <- edgeChildren edge
            , labelled <- rootEdges $ labelSupportWith original symbol child
            ]
    | [edge] <- edges
    , JoinN <- original (edgeSymbol edge) =
        Node [mkEdge symbol (edgeChildren edge) (edgeConstraint edge)]
    | isPureSupport original support = Node [Edge symbol []]
    | Just arguments <- applicationSupportChildren original support =
        Node [Edge symbol (toList arguments)]
    | otherwise = Node [Edge symbol [support]]
labelSupportWith original symbol support@(Mu _) = labelSupportWith original symbol $ unfoldOuterRec support
labelSupportWith _ symbol support = Node [Edge symbol [support]]

-- | Read the alternatives from one ordinary support node.
rootEdges :: (Typeable other) => Node other -> [Edge other]
rootEdges (Node edges) = edges
rootEdges _ = []

-- | Recognize the children of one private applicative support spine.
applicationSupportChildren ::
    (Typeable other) =>
    (other -> Label symbol) -> Node other -> Maybe (Seq (Node other))
applicationSupportChildren original (Node [edge])
    | Apply <- original (edgeSymbol edge)
    , unconstrainedEdge edge
    , [functions, argument] <- edgeChildren edge =
        Just $ applicationLeftSupport original functions :|> argument
applicationSupportChildren _ _ = Nothing

-- | Flatten the already-applied left portion of a support spine.
applicationLeftSupport ::
    (Typeable other) => (other -> Label symbol) -> Node other -> Seq (Node other)
applicationLeftSupport original support
    | isPureSupport original support = Empty
    | Just arguments <- applicationSupportChildren original support = arguments
    | otherwise = Sequence.singleton support

-- | Whether a support node is the nullary private applicative identity.
isPureSupport :: (Typeable other) => (other -> Label symbol) -> Node other -> Bool
isPureSupport original (Node [edge])
    | Pure <- original (edgeSymbol edge) =
        null (edgeChildren edge) && unconstrainedEdge edge
isPureSupport _ _ = False

-- | Whether an edge is one private single-child choice wrapper.
isChoiceEdge :: (other -> Label symbol) -> Edge other -> Bool
isChoiceEdge original edge
    | Choice _ <- original (edgeSymbol edge) =
        compareLength (edgeChildren edge) 1 == EQ && unconstrainedEdge edge
    | otherwise = False

-- | Close one private applicative term spine with a domain constructor.
labelTerm :: symbol -> Tree.Tree (Label symbol) -> Tree.Tree (Label symbol)
labelTerm symbol = labelTermWith id (Label symbol)

-- | Close a term layer by recognizing the private labels under a representation.
labelTermWith :: (other -> Label symbol) -> other -> Tree.Tree other -> Tree.Tree other
labelTermWith original symbol term@(Tree.Node internal children) =
    case original internal of
        JoinN -> Tree.Node symbol children
        Choice _ | [child] <- children -> labelTermWith original symbol child
        Pure -> Tree.Node symbol []
        _
            | Just arguments <- applicationTermChildren original term -> Tree.Node symbol $ toList arguments
            | otherwise -> Tree.Node symbol [term]

{- | The children that 'labelTerm' gives a term under a node label: the
arguments of an applicative spine, the children of an n-way join, or the term
itself. A choice wrapper gives the children of its alternative.
-}
labelledChildren :: Tree.Tree (Label symbol) -> [Tree.Tree (Label symbol)]
labelledChildren = Tree.subForest . labelTermWith id Pure

{- | The arguments that a term gives as the function side of an applicative
spine: none for @pure@, the arguments of a spine, or the term itself.
-}
spineChildren :: Tree.Tree (Label symbol) -> Seq (Tree.Tree (Label symbol))
spineChildren = applicationLeftChildren id

-- | Recognize the children of one private applicative term spine.
applicationTermChildren :: (other -> Label symbol) -> Tree.Tree other -> Maybe (Seq (Tree.Tree other))
applicationTermChildren original (Tree.Node internal [functions, argument])
    | Apply <- original internal =
        Just $ applicationLeftChildren original functions :|> argument
applicationTermChildren _ _ = Nothing

-- | Flatten the already-applied left portion of an applicative term spine.
applicationLeftChildren :: (other -> Label symbol) -> Tree.Tree other -> Seq (Tree.Tree other)
applicationLeftChildren original term@(Tree.Node internal children)
    | Pure <- original internal
    , null children =
        Empty
    | Just arguments <- applicationTermChildren original term = arguments
    | otherwise = Sequence.singleton term
