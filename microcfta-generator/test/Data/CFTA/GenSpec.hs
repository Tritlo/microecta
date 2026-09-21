{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeApplications #-}

module Data.CFTA.GenSpec (spec) where

import Control.Exception (evaluate)
import Data.Either (fromRight)
import Data.List (nub)
import Data.Proxy (Proxy (Proxy))
import Data.String (fromString)
import Data.Typeable (typeRep)
import GHC.Generics (Generic)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import Control.Monad (void)
import qualified Data.CFTA as Automaton
import qualified Data.CFTA.Gen.QuickCheck as FTAGen
import qualified Data.CFTA.Gen.UntypedExpressionLanguage as Expressions
import qualified Data.CFTA.Generic as Datatype
import qualified Data.CFTA.Interned as Common
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Symbol (Symbol)
import qualified Data.Tree as Tree

-- | A derived recursive fixture with named child positions.
data DerivedTree = Leaf Bool | Fork DerivedTree DerivedTree
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA DerivedTree

-- | A record fixture retains selector names without partial record fields.
data RecordPair = RecordPair {leftChild :: DerivedTree, rightChild :: DerivedTree}
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA RecordPair

-- | The first type in a mutually recursive fixture.
data MutualA = AEnd | AStep MutualB
    deriving (Eq, Show, Generic)

-- | The second type in a mutually recursive fixture.
data MutualB = BEnd | BStep MutualA
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA MutualA
instance Datatype.HasFTA MutualB

-- | An empty datatype has one state with no transitions.
data EmptyDatatype deriving (Generic)

instance Datatype.HasFTA EmptyDatatype

-- | Non-regular recursion would require an unbounded set of type states.
data Growing a = GrowEnd | Grow (Growing [a])
    deriving (Generic)

instance (Datatype.HasFTA a) => Datatype.HasFTA (Growing a)

atoms :: FTAGen.FTAGen String Int
atoms = FTAGen.oneof [FTAGen.leaf 0 "zero", FTAGen.leaf 1 "one"]

pairs :: FTAGen.FTAGen String (Int, Int)
pairs = FTAGen.node "pair" $ FTAGen.do
    left <- atoms
    right <- atoms
    FTAGen.pure (left, right)

spec :: Spec
spec = do
    describe "datatype-derived FTA generation" $ do
        it "derives one recursive grammar and preserves typed replay and shrinking" $
            case Datatype.deriveFTA @DerivedTree of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    let expected = [Leaf False, Leaf True] <> [Fork (Leaf left) (Leaf right) | left <- [False, True], right <- [False, True]]
                        check generator = do
                            FTAGen.cardinality generator `shouldBe` Right 6
                            traverse (FTAGen.unrank generator) [0 .. 5] `shouldBe` Right expected
                            traverse (FTAGen.termAt generator) [0 .. 5]
                                `shouldBe` Right (map (fmap constructorSymbol . Datatype.encodeTerm) expected)
                            map (Datatype.decodeTerm . Datatype.encodeTerm) expected
                                `shouldBe` map Just expected
                            FTAGen.shrinkRank generator 5 `shouldSatisfy` (not . null)
                            map (FTAGen.unrank generator) (FTAGen.shrinkRank generator 5)
                                `shouldSatisfy` all (`elem` map Right (take 5 expected))
                    length (Automaton.states $ Datatype.datatypeFTA datatype) `shouldBe` 2
                    check $ FTAGen.fromDatatypeUpToDepth 2 datatype
                    check $ FTAGen.upToSize 5 $ FTAGen.fromDatatype datatype

        it "retains record names, positions, and fully applied field types" $ do
            let Tree.Node constructor _ = Datatype.encodeTerm $ RecordPair (Leaf False) (Leaf True)
                typ = typeRep $ Proxy @DerivedTree
            Datatype.constructorName constructor `shouldBe` "RecordPair"
            Datatype.fieldNamed "rightChild" constructor
                `shouldBe` Just (Datatype.Field 1 (Just "rightChild") typ)
            (Datatype.decodeTerm (Tree.Node constructor []) :: Maybe DerivedTree) `shouldBe` Nothing
            (Datatype.decodeTerm (Datatype.encodeTerm True) :: Maybe DerivedTree) `shouldBe` Nothing

        it "reuses mutually recursive type states and accepts finite nested lists" $ do
            case Datatype.deriveFTA @MutualA of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    let generator = FTAGen.fromDatatypeUpToDepth 3 datatype
                     in traverse (FTAGen.unrank generator) [0 .. 3]
                            `shouldBe` Right [AEnd, AStep BEnd, AStep (BStep AEnd), AStep (BStep (AStep BEnd))]
            case Datatype.deriveFTA @[[Bool]] of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    Automaton.accepts (Datatype.datatypeFTA datatype) (Datatype.encodeTerm [[True], [], [False]]) `shouldBe` True

        it "requires explicit atomic domains and retains their order without duplicates" $ do
            void (Datatype.deriveFTA @(Maybe Int))
                `shouldBe` Left (Datatype.MissingDomain $ typeRep $ Proxy @Int)
            case Datatype.deriveFTAWith @(Maybe Int) $ Datatype.domain @Int [2, 1, 2] of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    traverse (FTAGen.unrank $ FTAGen.fromDatatypeUpToDepth 1 datatype) [0 .. 2]
                        `shouldBe` Right [Nothing, Just 2, Just 1]
            void (Datatype.deriveFTAWith @Bool $ Datatype.domain [False])
                `shouldBe` Left (Datatype.NonAtomicDomain $ typeRep $ Proxy @Bool)

        it "represents empty datatypes and rejects growing recursive type arguments" $ do
            case Datatype.deriveFTA @EmptyDatatype of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    FTAGen.cardinality (FTAGen.fromDatatypeUpToDepth 3 datatype)
                        `shouldBe` Left FTAGen.EmptyGenerator
            void (Datatype.deriveFTA @(Growing Bool))
                `shouldBe` Left (Datatype.NonRegularRecursion (typeRep $ Proxy @(Growing Bool)) (typeRep $ Proxy @(Growing [Bool])))

    describe "ordinary FTA generator syntax" $ do
        it "closes a single do binding as one direct constructor child" $ do
            let boxed = FTAGen.node "box" $ FTAGen.do
                    value <- atoms
                    FTAGen.pure $ value + 1
            FTAGen.cardinality boxed `shouldBe` Right 2
            FTAGen.unrank boxed 1 `shouldBe` Right 2
            FTAGen.termAt boxed 1
                `shouldBe` Right (Tree.Node (FTAGen.Label "box") [Tree.Node (FTAGen.Label "one") []])

        it "uses each do binding as one direct constructor child" $ do
            -- A child that is a choice keeps its alternative label, so equal
            -- values from different alternatives stay distinct terms.
            FTAGen.cardinality pairs `shouldBe` Right 4
            FTAGen.termAt pairs 2
                `shouldBe` Right
                    ( Tree.Node
                        (FTAGen.Label "pair")
                        [ Tree.Node (FTAGen.Choice 1) [Tree.Node (FTAGen.Label "one") []]
                        , Tree.Node (FTAGen.Choice 0) [Tree.Node (FTAGen.Label "zero") []]
                        ]
                    )

        it "builds exact support accepting the term of every rank" $
            case (FTAGen.support pairs, traverse (FTAGen.termAt pairs) [0 .. 3]) of
                (Right support, Right terms) -> do
                    terms `shouldSatisfy` all (acceptsPlain support)
                    acceptsPlain support (Tree.Node (FTAGen.Label "pair") [Tree.Node (FTAGen.Label "zero") []])
                        `shouldBe` False
                (Left err, _) -> expectationFailure $ show err
                (_, Left err) -> expectationFailure $ show err

    describe "ordinary FTA compilation" $ do
        it "indexes recursive runs by size and bounds them by depth" $ do
            let rows = [((), [Automaton.Transition "z" [] (), Automaton.Transition "s" [()] ()])]
                terms = take 5 $ iterate (\term -> Tree.Node "s" [term]) (Tree.Node "z" [])
            case Automaton.mkFTA () rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let node = Common.fromFTA automaton
                        check generator = do
                            FTAGen.cardinality generator `shouldBe` Right 5
                            traverse (FTAGen.unrank generator) [0 .. 4] `shouldBe` Right terms
                            map (FTAGen.sizeOfRank generator) [0 .. 4] `shouldBe` map Just [1 .. 5]
                            FTAGen.shrinkRank generator 4 `shouldSatisfy` (not . null)
                            map (FTAGen.unrank generator) (FTAGen.shrinkRank generator 4)
                                `shouldSatisfy` all (`elem` map Right (take 4 terms))
                    check $ FTAGen.upToSize 5 $ FTAGen.fromAutomaton node
                    check $ FTAGen.fromAutomatonUpToDepth 4 node
                    FTAGen.cardinality (FTAGen.upToSize 0 $ FTAGen.fromAutomaton node)
                        `shouldBe` Left FTAGen.EmptyGenerator

        it "keeps empty recursion distinct from ambiguity and counts distinct finite terms" $ do
            let rows =
                    [ (0 :: Int, [Automaton.Transition "step" [1] ()])
                    , (1, [Automaton.Transition "again" [0] ()])
                    ]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right empty ->
                    FTAGen.cardinality (FTAGen.upToSize 10 $ FTAGen.fromAutomaton $ Common.fromFTA empty)
                        `shouldBe` Left FTAGen.EmptyGenerator
            let productive =
                    [ (0 :: Int, [Automaton.Transition "z" [] (), Automaton.Transition "step" [1] (), Automaton.Transition "step" [2] ()])
                    , (1, [Automaton.Transition "again" [0] (), Automaton.Transition "extra" [] ()])
                    , (2, [Automaton.Transition "again" [0] ()])
                    ]
            case Automaton.mkFTA 0 productive of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    -- Size counting sums over accepting runs, so it rejects
                    -- the ambiguous recursion; the finite bound counts each
                    -- distinct term once.
                    let node = Common.fromFTA automaton
                        bounded = FTAGen.fromAutomatonUpToDepth 4 node
                    FTAGen.cardinality (FTAGen.upToSize 5 $ FTAGen.fromAutomaton node)
                        `shouldBe` Left FTAGen.AmbiguousAutomaton
                    FTAGen.cardinality bounded `shouldBe` Right 5
                    fmap (length . nub) (traverse (FTAGen.unrank bounded) [0 .. 4])
                        `shouldBe` Right 5

        it "compiles the common interned unit-constraint graph without ECTA" $ do
            let leaves = Common.Node [Common.Edge "zero" [], Common.Edge "one" []] :: Common.PlainNode String
                root = Common.Node [Common.Edge "pair" [leaves, leaves]]
                expected =
                    [ Tree.Node "pair" [Tree.Node left [], Tree.Node right []]
                    | left <- ["zero", "one"]
                    , right <- ["zero", "one"]
                    ]
                generator = FTAGen.fromAutomaton root
            case Common.toFTA root of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    FTAGen.cardinality generator `shouldBe` Right 4
                    traverse (FTAGen.unrank generator) [0 .. 3] `shouldBe` Right expected
                    all (Automaton.accepts automaton) expected `shouldBe` True

        it "shares state compilation and decoding across a large finite DAG" $ do
            let depth = 64 :: Int
                rows =
                    (0, [Automaton.Transition "z" [] ()])
                        : [ (state, [Automaton.Transition "a" [state - 1] (), Automaton.Transition "b" [state - 1] ()])
                          | state <- [1 .. depth]
                          ]
                chain symbol = iterate (\term -> Tree.Node symbol [term]) (Tree.Node "z" []) !! depth
            case Automaton.mkFTA depth rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let generator = FTAGen.fromAutomaton $ Common.fromFTA automaton
                    completed <-
                        timeout 60000000
                            $ evaluate
                            $ FTAGen.cardinality generator == Right (2 ^ depth)
                                && FTAGen.unrank generator 0 == Right (chain "a")
                                && FTAGen.unrank generator (2 ^ depth - 1) == Right (chain "b")
                    completed `shouldBe` Just True

        it "preserves ranks and structural shrinking through shared states" $ do
            let rows =
                    [ (0, [Automaton.Transition "x" [] (), Automaton.Transition "y" [] ()])
                    , (1, [Automaton.Transition "a" [] (), Automaton.Transition "wrap" [0] ()])
                    , (2, [Automaton.Transition "pair" [1, 1] ()])
                    ]
                reference = do
                    leaves <- Ranked.oneof [pure $ Tree.Node "x" [], pure $ Tree.Node "y" []]
                    alternatives <-
                        Ranked.oneof
                            [ pure $ Tree.Node "a" []
                            , pure (\child -> Tree.Node "wrap" [child]) <*> leaves
                            ]
                    pure $ pure (\left right -> Tree.Node "pair" [left, right]) <*> alternatives <*> alternatives
            case Automaton.mkFTA (2 :: Int) rows of
                Left err -> expectationFailure $ show err
                Right automaton -> case reference of
                    Left err -> expectationFailure $ show err
                    Right expected -> do
                        let actual = FTAGen.fromAutomaton $ Common.fromFTA automaton
                            ranks = [0 .. Ranked.cardinality expected - 1]
                            members = either (const Nothing) Just
                        FTAGen.cardinality actual `shouldBe` Right (Ranked.cardinality expected)
                        members (traverse (FTAGen.unrank actual) ranks) `shouldBe` members (traverse (Ranked.unrank expected) ranks)
                        map (FTAGen.sizeOfRank actual) ranks `shouldBe` map (Ranked.sizeOfRank expected) ranks
                        map (FTAGen.shrinkRank actual) ranks `shouldBe` map (Ranked.shrinkRank expected) ranks
                        map (FTAGen.smallerMembers actual) ranks `shouldBe` map (Ranked.smallerMembers expected) ranks

    describe "ordinary FTA integer expressions" $ do
        it "has the exact structural cardinality at every bounded depth" $
            map (FTAGen.cardinality . Expressions.expressionsAtDepth) [0 .. 4]
                `shouldBe` map (Right . Expressions.expressionCount) [0 .. 4]

        it "generates executable expressions without type-side conditions" $ do
            let expressions = Expressions.expressionsAtDepth 2
                total = fromRight 0 $ FTAGen.cardinality expressions
                generated =
                    [ expression
                    | rank <- [0 .. total - 1]
                    , Right expression <- [FTAGen.unrank expressions rank]
                    ]
            length generated `shouldBe` fromInteger total
            generated `shouldSatisfy` all ((>= 0) . Expressions.evaluate)

        modifyMaxSuccess (const 500)
            $ it "keeps both reference generators in the exact-depth language"
            $ QC.conjoin
                [ QC.forAll (generator 3) $ \expression ->
                    QC.counterexample (show expression) $
                        expressionDepth expression QC.=== 3
                | generator <-
                    [ Expressions.naiveExpressionGen
                    , Expressions.handwrittenExpressionGen
                    ]
                ]

-- | Number of constructor layers in an untyped expression.
expressionDepth :: Expressions.Expression -> Int
expressionDepth (Expressions.Literal _) = 0
expressionDepth (Expressions.Add left right) =
    1 + max (expressionDepth left) (expressionDepth right)
expressionDepth (Expressions.Multiply left right) =
    1 + max (expressionDepth left) (expressionDepth right)

-- | Membership in a plain interned support.
acceptsPlain :: Common.PlainNode (FTAGen.Label String) -> Tree.Tree (FTAGen.Label String) -> Bool
acceptsPlain = Common.acceptsWith (\() _ -> True)

-- | The generator symbol of a derived constructor.
constructorSymbol :: Datatype.Constructor -> FTAGen.Label Symbol
constructorSymbol = FTAGen.Label . fromString . Datatype.constructorLabel
