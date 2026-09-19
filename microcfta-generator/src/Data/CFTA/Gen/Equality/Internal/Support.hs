{-# LANGUAGE OverloadedStrings #-}

{- | The private ECTA symbols and support nodes the generator engine builds.

The engine labels an open child layer with its own namespaced symbols. The
labelling functions replace that scaffolding with one domain constructor when
@node@ closes the layer, so a generated term holds user symbols only.
-}
module Data.CFTA.Gen.Equality.Internal.Support (
    -- * Symbols
    pureSymbol,
    applySymbol,
    joinSymbol,
    joinNSymbol,
    centerKeyedSymbol,
    leftKeyedSymbol,
    rightKeyedSymbol,
    argKeyedSymbol,
    familySymbol,
    keyRestrictSymbol,
    indexedSymbol,
    frequencySymbol,
    keySymbol,
    argKeySymbol,

    -- * Support nodes
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
) where

import Data.Hashable (Hashable)
import Data.List (compareLength)
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import Data.Typeable (Typeable)

import Data.CFTA.Constraint.Equality (EqConstraints (EmptyConstraints), mkEqConstraints)
import Data.CFTA.Equality (
    Edge (Edge),
    Node (Mu, Node),
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    mkEdge,
    unfoldOuterRec,
 )
import Data.CFTA.Path (path)
import Data.CFTA.Symbol (Symbol (Symbol))

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
keyNode :: Int -> Node Symbol EqConstraints
keyNode index = Node [Edge (keySymbol index) []]

-- | The ECTA node accepting exactly one term.
singletonNode :: (Hashable symbol, Typeable symbol) => Tree.Tree symbol -> Node symbol EqConstraints
singletonNode = Tree.foldTree $ \symbol children -> Node [Edge symbol children]

{- | One joined edge: the operation group, one group per argument, and one
equality constraint per argument tying each argument to the operation's key
at that position.
-}
joinNode :: Int -> Node Symbol EqConstraints -> [Node Symbol EqConstraints] -> Node Symbol EqConstraints
joinNode = joinNodeWith id

-- | Build a joined support with a caller-supplied representation of private symbols.
joinNodeWith ::
    (Hashable symbol, Typeable symbol) =>
    (Symbol -> symbol) ->
    Int ->
    Node symbol EqConstraints ->
    [Node symbol EqConstraints] ->
    Node symbol EqConstraints
joinNodeWith inject componentIndex operationSupport argumentSupports =
    Node
        [ mkEdge
            (inject joinNSymbol)
            (operationNode : argumentNodes)
            ( mkEqConstraints
                [ [path [0, position], path [position + 1, 0]]
                | position <- [0 .. length argumentSupports - 1]
                ]
            )
        ]
  where
    keyNodes =
        [ singletonNode $ Tree.Node (inject $ argKeySymbol componentIndex position) []
        | position <- [0 .. length argumentSupports - 1]
        ]
    operationNode =
        Node [Edge (inject centerKeyedSymbol) (keyNodes <> [operationSupport])]
    argumentNodes =
        [ Node [Edge (inject argKeyedSymbol) [argKeyNode, argumentSupport]]
        | (argKeyNode, argumentSupport) <- zip keyNodes argumentSupports
        ]

{- | Restrict a recursive family to one key.

A recursive family is one @Mu@ whose edges carry their key as a first child,
so an occurrence at one key is the family under an edge holding that key's
label, with a constraint equating the two. The discrimination is the
automaton's own, which is what lets the whole family share one binder.
-}
restrictToKey :: Int -> Node Symbol EqConstraints -> Node Symbol EqConstraints
restrictToKey = restrictToKeyWith id

-- | Restrict a recursive family with a caller-supplied representation of private symbols.
restrictToKeyWith ::
    (Hashable symbol, Typeable symbol) =>
    (Symbol -> symbol) -> Int -> Node symbol EqConstraints -> Node symbol EqConstraints
restrictToKeyWith inject position family =
    Node
        [ mkEdge
            (inject keyRestrictSymbol)
            [singletonNode $ Tree.Node (inject $ keySymbol position) [], family]
            (mkEqConstraints [[path [0], path [1, 0]]])
        ]

-- | One recursive family node: one key-labelled edge per key, in key order.
familyNode :: [(Int, Node Symbol EqConstraints)] -> Node Symbol EqConstraints
familyNode = familyNodeWith id

-- | Build a recursive family with a caller-supplied representation of private symbols.
familyNodeWith ::
    (Hashable symbol, Typeable symbol) =>
    (Symbol -> symbol) -> [(Int, Node symbol EqConstraints)] -> Node symbol EqConstraints
familyNodeWith inject keyed =
    Node
        [ Edge (inject familySymbol) [singletonNode $ Tree.Node (inject $ keySymbol position) [], body]
        | (position, body) <- keyed
        ]

-- | Close one private support root while preserving its constraints.
labelSupport :: Symbol -> Node Symbol EqConstraints -> Node Symbol EqConstraints
labelSupport = labelSupportWith id

-- | Close a support layer by recognizing the original private symbols.
labelSupportWith ::
    (Hashable symbol, Typeable symbol) =>
    (symbol -> Symbol) -> symbol -> Node symbol EqConstraints -> Node symbol EqConstraints
labelSupportWith original symbol support@(Node edges)
    | not (null edges)
    , all (isFrequencyEdge original) edges =
        Node
            [ labelled
            | edge <- edges
            , child <- edgeChildren edge
            , labelled <- rootEdges $ labelSupportWith original symbol child
            ]
    | [edge] <- edges
    , original (edgeSymbol edge) == joinNSymbol =
        Node [mkEdge symbol (edgeChildren edge) (edgeConstraint edge)]
    | isPureSupport original support = Node [Edge symbol []]
    | Just arguments <- applicationSupportChildren original support =
        Node [Edge symbol arguments]
    | otherwise = Node [Edge symbol [support]]
labelSupportWith original symbol support@(Mu _) = labelSupportWith original symbol $ unfoldOuterRec support
labelSupportWith _ symbol support = Node [Edge symbol [support]]

-- | Read the alternatives from one ordinary support node.
rootEdges :: (Typeable symbol) => Node symbol EqConstraints -> [Edge symbol EqConstraints]
rootEdges (Node edges) = edges
rootEdges _ = []

-- | Recognize the children of one private applicative support spine.
applicationSupportChildren ::
    (Typeable symbol) => (symbol -> Symbol) -> Node symbol EqConstraints -> Maybe [Node symbol EqConstraints]
applicationSupportChildren original (Node [edge])
    | original (edgeSymbol edge) == applySymbol
    , edgeConstraint edge == EmptyConstraints
    , [functions, argument] <- edgeChildren edge =
        Just $ applicationLeftSupport original functions <> [argument]
applicationSupportChildren _ _ = Nothing

-- | Flatten the already-applied left portion of a support spine.
applicationLeftSupport ::
    (Typeable symbol) => (symbol -> Symbol) -> Node symbol EqConstraints -> [Node symbol EqConstraints]
applicationLeftSupport original support
    | isPureSupport original support = []
    | Just arguments <- applicationSupportChildren original support = arguments
    | otherwise = [support]

-- | Whether a support node is the nullary private applicative identity.
isPureSupport :: (Typeable symbol) => (symbol -> Symbol) -> Node symbol EqConstraints -> Bool
isPureSupport original (Node [edge]) =
    original (edgeSymbol edge) == pureSymbol
        && null (edgeChildren edge)
        && edgeConstraint edge == EmptyConstraints
isPureSupport _ _ = False

-- | Whether an edge is one private single-child choice wrapper.
isFrequencyEdge :: (symbol -> Symbol) -> Edge symbol EqConstraints -> Bool
isFrequencyEdge original edge =
    isFrequencySymbol (original $ edgeSymbol edge)
        && compareLength (edgeChildren edge) 1 == EQ
        && edgeConstraint edge == EmptyConstraints

-- | Close one private applicative term spine with a domain constructor.
labelTerm :: Symbol -> Tree.Tree Symbol -> Tree.Tree Symbol
labelTerm = labelTermWith id

-- | Close a term layer by recognizing the original private symbols.
labelTermWith :: (symbol -> Symbol) -> symbol -> Tree.Tree symbol -> Tree.Tree symbol
labelTermWith original symbol term@(Tree.Node internal children)
    | original internal == joinNSymbol = Tree.Node symbol children
    | isFrequencySymbol $ original internal
    , [child] <- children =
        labelTermWith original symbol child
    | original internal == pureSymbol = Tree.Node symbol []
    | Just arguments <- applicationTermChildren original term = Tree.Node symbol arguments
    | otherwise = Tree.Node symbol [term]

-- | Recognize the children of one private applicative term spine.
applicationTermChildren :: (symbol -> Symbol) -> Tree.Tree symbol -> Maybe [Tree.Tree symbol]
applicationTermChildren original (Tree.Node internal [functions, argument])
    | original internal == applySymbol =
        Just $ applicationLeftChildren original functions <> [argument]
applicationTermChildren _ _ = Nothing

-- | Flatten the already-applied left portion of an applicative term spine.
applicationLeftChildren :: (symbol -> Symbol) -> Tree.Tree symbol -> [Tree.Tree symbol]
applicationLeftChildren original term@(Tree.Node internal children)
    | original internal == pureSymbol && null children = []
    | Just arguments <- applicationTermChildren original term = arguments
    | otherwise = [term]
