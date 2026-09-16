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
import qualified Data.Text as Text
import Data.Typeable (Typeable)

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
import Data.ECTA.Term (Symbol (Symbol), Term (Term))

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
singletonNode :: (Hashable symbol, Typeable symbol) => Term symbol -> Node symbol
singletonNode (Term symbol children) =
    Node [Edge symbol $ map singletonNode children]

{- | One joined edge: the operation group, one group per argument, and one
equality constraint per argument tying each argument to the operation's key
at that position.
-}
joinNode :: Int -> Node Symbol -> [Node Symbol] -> Node Symbol
joinNode = joinNodeWith id

-- | Build a joined support with a caller-supplied representation of private symbols.
joinNodeWith ::
    (Hashable symbol, Typeable symbol) =>
    (Symbol -> symbol) ->
    Int ->
    Node symbol ->
    [Node symbol] ->
    Node symbol
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
        [ singletonNode $ Term (inject $ argKeySymbol componentIndex position) []
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
restrictToKey :: Int -> Node Symbol -> Node Symbol
restrictToKey = restrictToKeyWith id

-- | Restrict a recursive family with a caller-supplied representation of private symbols.
restrictToKeyWith ::
    (Hashable symbol, Typeable symbol) =>
    (Symbol -> symbol) -> Int -> Node symbol -> Node symbol
restrictToKeyWith inject position family =
    Node
        [ mkEdge
            (inject keyRestrictSymbol)
            [singletonNode $ Term (inject $ keySymbol position) [], family]
            (mkEqConstraints [[path [0], path [1, 0]]])
        ]

-- | One recursive family node: one key-labelled edge per key, in key order.
familyNode :: [(Int, Node Symbol)] -> Node Symbol
familyNode = familyNodeWith id

-- | Build a recursive family with a caller-supplied representation of private symbols.
familyNodeWith ::
    (Hashable symbol, Typeable symbol) =>
    (Symbol -> symbol) -> [(Int, Node symbol)] -> Node symbol
familyNodeWith inject keyed =
    Node
        [ Edge (inject familySymbol) [singletonNode $ Term (inject $ keySymbol position) [], body]
        | (position, body) <- keyed
        ]

-- | Close one private support root while preserving its constraints.
labelSupport :: Symbol -> Node Symbol -> Node Symbol
labelSupport = labelSupportWith id

-- | Close a support layer by recognizing the original private symbols.
labelSupportWith ::
    (Hashable symbol, Typeable symbol) =>
    (symbol -> Symbol) -> symbol -> Node symbol -> Node symbol
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
        Node [mkEdge symbol (edgeChildren edge) (edgeEcs edge)]
    | isPureSupport original support = Node [Edge symbol []]
    | Just arguments <- applicationSupportChildren original support =
        Node [Edge symbol arguments]
    | otherwise = Node [Edge symbol [support]]
labelSupportWith original symbol support@(Mu _) = labelSupportWith original symbol $ unfoldOuterRec support
labelSupportWith _ symbol support = Node [Edge symbol [support]]

-- | Read the alternatives from one ordinary support node.
rootEdges :: (Typeable symbol) => Node symbol -> [Edge symbol]
rootEdges (Node edges) = edges
rootEdges _ = []

-- | Recognize the children of one private applicative support spine.
applicationSupportChildren ::
    (Typeable symbol) => (symbol -> Symbol) -> Node symbol -> Maybe [Node symbol]
applicationSupportChildren original (Node [edge])
    | original (edgeSymbol edge) == applySymbol
    , edgeEcs edge == EmptyConstraints
    , [functions, argument] <- edgeChildren edge =
        Just $ applicationLeftSupport original functions <> [argument]
applicationSupportChildren _ _ = Nothing

-- | Flatten the already-applied left portion of a support spine.
applicationLeftSupport :: (Typeable symbol) => (symbol -> Symbol) -> Node symbol -> [Node symbol]
applicationLeftSupport original support
    | isPureSupport original support = []
    | Just arguments <- applicationSupportChildren original support = arguments
    | otherwise = [support]

-- | Whether a support node is the nullary private applicative identity.
isPureSupport :: (Typeable symbol) => (symbol -> Symbol) -> Node symbol -> Bool
isPureSupport original (Node [edge]) =
    original (edgeSymbol edge) == pureSymbol
        && null (edgeChildren edge)
        && edgeEcs edge == EmptyConstraints
isPureSupport _ _ = False

-- | Whether an edge is one private single-child choice wrapper.
isFrequencyEdge :: (symbol -> Symbol) -> Edge symbol -> Bool
isFrequencyEdge original edge =
    isFrequencySymbol (original $ edgeSymbol edge)
        && length (edgeChildren edge) == 1
        && edgeEcs edge == EmptyConstraints

-- | Close one private applicative term spine with a domain constructor.
labelTerm :: Symbol -> Term Symbol -> Term Symbol
labelTerm = labelTermWith id

-- | Close a term layer by recognizing the original private symbols.
labelTermWith :: (symbol -> Symbol) -> symbol -> Term symbol -> Term symbol
labelTermWith original symbol term@(Term internal children)
    | original internal == joinNSymbol = Term symbol children
    | isFrequencySymbol $ original internal
    , [child] <- children =
        labelTermWith original symbol child
    | original internal == pureSymbol = Term symbol []
    | Just arguments <- applicationTermChildren original term = Term symbol arguments
    | otherwise = Term symbol [term]

-- | Recognize the children of one private applicative term spine.
applicationTermChildren :: (symbol -> Symbol) -> Term symbol -> Maybe [Term symbol]
applicationTermChildren original (Term internal [functions, argument])
    | original internal == applySymbol =
        Just $ applicationLeftChildren original functions <> [argument]
applicationTermChildren _ _ = Nothing

-- | Flatten the already-applied left portion of an applicative term spine.
applicationLeftChildren :: (symbol -> Symbol) -> Term symbol -> [Term symbol]
applicationLeftChildren original term@(Term internal children)
    | original internal == pureSymbol && null children = []
    | Just arguments <- applicationTermChildren original term = arguments
    | otherwise = [term]
