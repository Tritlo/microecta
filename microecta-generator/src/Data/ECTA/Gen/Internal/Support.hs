{-# LANGUAGE OverloadedStrings #-}

{- | The private ECTA symbols and support nodes the generator engine builds.

The engine labels an open child layer with its own namespaced symbols. The
labelling functions replace that scaffolding with one domain constructor when
@node@ closes the layer, so a generated term holds user symbols only.
-}
module Data.ECTA.Gen.Internal.Support (
    -- * Symbols
    pureSymbol,
    applySymbol,
    joinSymbol,
    joinNSymbol,
    centerKeyedSymbol,
    leftKeyedSymbol,
    rightKeyedSymbol,
    argKeyedSymbol,
    indexedSymbol,
    frequencySymbol,
    keySymbol,
    argKeySymbol,

    -- * Support nodes
    keyNode,
    singletonNode,
    joinNode,
    restrictToKey,
    familyNode,

    -- * Closing a layer
    labelSupport,
    labelTerm,
) where

import qualified Data.Text as Text
import qualified Data.Tree as Tree

import Data.ECTA (
    Edge (Edge),
    Node (Node),
    edgeChildren,
    edgeEcs,
    edgeSymbol,
    mkEdge,
 )
import Data.ECTA.Internal.ECTA.Operations (unfoldOuterRec)
import Data.ECTA.Internal.ECTA.Type (Node (Mu))
import Data.ECTA.Paths (EqConstraints (EmptyConstraints), mkEqConstraints, path)
import Data.ECTA.Term (Symbol (Symbol))

{- | Symbols labelling the ECTA structure this module builds. They are
namespaced so generated supports cannot collide with user symbols.
-}
pureSymbol
    , applySymbol
    , joinSymbol
    , joinNSymbol
    , centerKeyedSymbol
    , leftKeyedSymbol
    , rightKeyedSymbol
    , argKeyedSymbol
    , familySymbol
    , keyRestrictSymbol ::
        Symbol
pureSymbol = "$ecta-gen/pure"
applySymbol = "$ecta-gen/apply"
joinSymbol = "$ecta-gen/join"
centerKeyedSymbol = "$ecta-gen/center-keyed"
leftKeyedSymbol = "$ecta-gen/left-keyed"
rightKeyedSymbol = "$ecta-gen/right-keyed"
joinNSymbol = "$ecta-gen/join-n"
argKeyedSymbol = "$ecta-gen/arg-keyed"
familySymbol = "$ecta-gen/family"
keyRestrictSymbol = "$ecta-gen/at-key"

-- | Leaf symbol carrying one stable source index.
indexedSymbol :: Integer -> Symbol
indexedSymbol index = Symbol $ Text.pack $ "$ecta-gen/index/" <> show index

-- | Branch symbol carrying one alternative index.
frequencySymbol :: Int -> Symbol
frequencySymbol index = Symbol $ Text.pack $ "$ecta-gen/frequency/" <> show index

-- | Key symbol shared by one matched group.
keySymbol :: Int -> Symbol
keySymbol index = Symbol $ Text.pack $ "$ecta-gen/key/" <> show index

-- | Key symbol for one argument position of one joined component.
argKeySymbol :: Int -> Int -> Symbol
argKeySymbol componentIndex position =
    Symbol
        $ Text.pack
        $ "$ecta-gen/key/" <> show componentIndex <> "/" <> show position

-- | Whether a symbol names one private choice wrapper.
isFrequencySymbol :: Symbol -> Bool
isFrequencySymbol (Symbol name) = "$ecta-gen/frequency/" `Text.isPrefixOf` name

-- | Singleton key node labelling one matched group.
keyNode :: Int -> Node Symbol
keyNode index = Node [Edge (keySymbol index) []]

-- | The ECTA node accepting exactly one term.
singletonNode :: Tree.Tree Symbol -> Node Symbol
singletonNode (Tree.Node symbol children) =
    Node [Edge symbol $ map singletonNode children]

{- | One joined edge: the operation group, one group per argument, and one
equality constraint per argument tying each argument to the operation's key
at that position.
-}
joinNode :: Int -> Node Symbol -> [Node Symbol] -> Node Symbol
joinNode componentIndex operationSupport argumentSupports =
    Node
        [ mkEdge
            joinNSymbol
            (operationNode : argumentNodes)
            ( mkEqConstraints
                [ [path [0, position], path [position + 1, 0]]
                | position <- [0 .. length argumentSupports - 1]
                ]
            )
        ]
  where
    keyNodes =
        [ singletonNode $ Tree.Node (argKeySymbol componentIndex position) []
        | position <- [0 .. length argumentSupports - 1]
        ]
    operationNode =
        Node [Edge centerKeyedSymbol (keyNodes <> [operationSupport])]
    argumentNodes =
        [ Node [Edge argKeyedSymbol [argKeyNode, argumentSupport]]
        | (argKeyNode, argumentSupport) <- zip keyNodes argumentSupports
        ]

{- | Restrict a recursive family to one key.

A recursive family is one @Mu@ whose edges carry their key as a first child,
so an occurrence at one key is the family under an edge holding that key's
label, with a constraint equating the two. The discrimination is the
automaton's own, which is what lets the whole family share one binder.
-}
restrictToKey :: Int -> Node Symbol -> Node Symbol
restrictToKey position family =
    Node
        [ mkEdge
            keyRestrictSymbol
            [keyNode position, family]
            (mkEqConstraints [[path [0], path [1, 0]]])
        ]

-- | One recursive family node: one key-labelled edge per key, in key order.
familyNode :: [(Int, Node Symbol)] -> Node Symbol
familyNode keyed =
    Node [Edge familySymbol [keyNode position, body] | (position, body) <- keyed]

-- | Close one private support root while preserving its constraints.
labelSupport :: Symbol -> Node Symbol -> Node Symbol
labelSupport symbol support@(Node edges)
    | not (null edges)
    , all isFrequencyEdge edges =
        Node
            [ labelled
            | edge <- edges
            , child <- edgeChildren edge
            , labelled <- rootEdges $ labelSupport symbol child
            ]
    | [edge] <- edges
    , edgeSymbol edge == joinNSymbol =
        Node [mkEdge symbol (edgeChildren edge) (edgeEcs edge)]
    | isPureSupport support = Node [Edge symbol []]
    | Just arguments <- applicationSupportChildren support =
        Node [Edge symbol arguments]
    | otherwise = Node [Edge symbol [support]]
labelSupport symbol support@(Mu _) = labelSupport symbol $ unfoldOuterRec support
labelSupport symbol support = Node [Edge symbol [support]]

-- | Read the alternatives from one ordinary support node.
rootEdges :: Node Symbol -> [Edge Symbol]
rootEdges (Node edges) = edges
rootEdges _ = []

-- | Recognize the children of one private applicative support spine.
applicationSupportChildren :: Node Symbol -> Maybe [Node Symbol]
applicationSupportChildren (Node [edge])
    | edgeSymbol edge == applySymbol
    , edgeEcs edge == EmptyConstraints
    , [functions, argument] <- edgeChildren edge =
        Just $ applicationLeftSupport functions <> [argument]
applicationSupportChildren _ = Nothing

-- | Flatten the already-applied left portion of a support spine.
applicationLeftSupport :: Node Symbol -> [Node Symbol]
applicationLeftSupport support
    | isPureSupport support = []
    | Just arguments <- applicationSupportChildren support = arguments
    | otherwise = [support]

-- | Whether a support node is the nullary private applicative identity.
isPureSupport :: Node Symbol -> Bool
isPureSupport (Node [edge]) =
    edgeSymbol edge == pureSymbol
        && null (edgeChildren edge)
        && edgeEcs edge == EmptyConstraints
isPureSupport _ = False

-- | Whether an edge is one private single-child choice wrapper.
isFrequencyEdge :: Edge Symbol -> Bool
isFrequencyEdge edge =
    isFrequencySymbol (edgeSymbol edge)
        && compareLength (edgeChildren edge) 1 == EQ
        && edgeEcs edge == EmptyConstraints

-- | Close one private applicative term spine with a domain constructor.
labelTerm :: Symbol -> Tree.Tree Symbol -> Tree.Tree Symbol
labelTerm symbol term@(Tree.Node internal children)
    | internal == joinNSymbol = Tree.Node symbol children
    | isFrequencySymbol internal
    , [child] <- children =
        labelTerm symbol child
    | internal == pureSymbol = Tree.Node symbol []
    | Just arguments <- applicationTermChildren term = Tree.Node symbol arguments
    | otherwise = Tree.Node symbol [term]

-- | Recognize the children of one private applicative term spine.
applicationTermChildren :: Tree.Tree Symbol -> Maybe [Tree.Tree Symbol]
applicationTermChildren (Tree.Node internal [functions, argument])
    | internal == applySymbol =
        Just $ applicationLeftChildren functions <> [argument]
applicationTermChildren _ = Nothing

-- | Flatten the already-applied left portion of an applicative term spine.
applicationLeftChildren :: Tree.Tree Symbol -> [Tree.Tree Symbol]
applicationLeftChildren term@(Tree.Node internal children)
    | internal == pureSymbol && null children = []
    | Just arguments <- applicationTermChildren term = arguments
    | otherwise = [term]
