{-# LANGUAGE OverloadedStrings #-}

{- | The private ECTA symbols and support nodes the generator engine builds.

The engine uses private symbols to retain products, choices, and equality joins.
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
) where

import qualified Data.Text as Text

import Data.ECTA (
    Edge (Edge),
    Node (Node),
    mkEdge,
 )
import Data.ECTA.Paths (mkEqConstraints, path)
import Data.ECTA.Term (Symbol (Symbol), Term (Term))

{- | Symbols labelling the ECTA structure this module builds. They are
namespaced so generated supports cannot collide with user symbols.
-}
pureSymbol, applySymbol, joinSymbol, joinNSymbol, centerKeyedSymbol, leftKeyedSymbol, rightKeyedSymbol, argKeyedSymbol, familySymbol, keyRestrictSymbol :: Symbol
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

-- | Singleton key node labelling one matched group.
keyNode :: Int -> Node Symbol
keyNode index = Node [Edge (keySymbol index) []]

-- | The ECTA node accepting exactly one term.
singletonNode :: Term Symbol -> Node Symbol
singletonNode (Term symbol children) =
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
        [ singletonNode $ Term (argKeySymbol componentIndex position) []
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
