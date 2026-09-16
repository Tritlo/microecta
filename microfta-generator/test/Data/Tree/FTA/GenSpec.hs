{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE TypeApplications #-}

module Data.Tree.FTA.GenSpec (spec) where

import Control.Exception (evaluate)
import Data.List (nub)
import Data.Proxy (Proxy (Proxy))
import Data.Typeable (typeRep)
import GHC.Generics (Generic)
import System.Timeout (timeout)
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import Control.Monad (void)
import qualified Data.Tree.FTA as Automaton
import qualified Data.Tree.FTA.Gen.QuickCheck as FTA
import qualified Data.Tree.FTA.Generic as Datatype
import qualified Data.Tree.FTA.Interned as Common
import qualified Data.Tree.FTA.UntypedExpressionLanguage as Expressions
import qualified Data.Tree.Gen as Ranked
import Data.Tree.Term (pattern Term)

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

atoms :: FTA.FTAGen String Int
atoms =
    case FTA.oneof [FTA.leaf "zero" 0, FTA.leaf "one" 1] of
        Left err -> error $ show err
        Right generator -> generator

pairs :: FTA.FTAGen String (Int, Int)
pairs = FTA.node "pair" $ FTA.do
    left <- atoms
    right <- atoms
    FTA.pure (left, right)

spec :: Spec
spec = do
    describe "datatype-derived FTA generation" $ do
        it "derives one recursive grammar and preserves typed replay and shrinking" $
            case Datatype.deriveFTA @DerivedTree of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    let expected = [Leaf False, Leaf True] <> [Fork (Leaf left) (Leaf right) | left <- [False, True], right <- [False, True]]
                        check result = case result of
                            Left err -> expectationFailure $ show err
                            Right generator -> do
                                FTA.cardinality generator `shouldBe` 6
                                traverse (FTA.unrank generator) [0 .. 5] `shouldBe` Right expected
                                traverse (FTA.generatedTerm generator) [0 .. 5]
                                    `shouldBe` Right (map Datatype.encodeTerm expected)
                                map (Datatype.decodeTerm . Datatype.encodeTerm) expected
                                    `shouldBe` map Just expected
                                let ranked = FTA.toRanked generator
                                Ranked.shrinkRank ranked 5 `shouldSatisfy` (not . null)
                                map (Ranked.unrank ranked) (Ranked.shrinkRank ranked 5)
                                    `shouldSatisfy` all (`elem` map Right (take 5 expected))
                    length (Automaton.states $ Datatype.datatypeFTA datatype) `shouldBe` 2
                    check $ FTA.fromDatatypeUpToDepth 2 datatype
                    check $ FTA.fromDatatypeUpToSize 5 datatype

        it "retains record names, positions, and fully applied field types" $ do
            let Term constructor _ = Datatype.encodeTerm $ RecordPair (Leaf False) (Leaf True)
                typ = typeRep $ Proxy @DerivedTree
            Datatype.constructorName constructor `shouldBe` "RecordPair"
            Datatype.fieldNamed "rightChild" constructor
                `shouldBe` Just (Datatype.Field 1 (Just "rightChild") typ)
            (Datatype.decodeTerm (Term constructor []) :: Maybe DerivedTree) `shouldBe` Nothing
            (Datatype.decodeTerm (Datatype.encodeTerm True) :: Maybe DerivedTree) `shouldBe` Nothing

        it "reuses mutually recursive type states and accepts finite nested lists" $ do
            case Datatype.deriveFTA @MutualA of
                Left err -> expectationFailure $ show err
                Right datatype -> case FTA.fromDatatypeUpToDepth 3 datatype of
                    Left err -> expectationFailure $ show err
                    Right generator ->
                        traverse (FTA.unrank generator) [0 .. 3]
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
                Right datatype -> case FTA.fromDatatypeUpToDepth 1 datatype of
                    Left err -> expectationFailure $ show err
                    Right generator ->
                        traverse (FTA.unrank generator) [0 .. 2] `shouldBe` Right [Nothing, Just 2, Just 1]
            void (Datatype.deriveFTAWith @Bool $ Datatype.domain [False])
                `shouldBe` Left (Datatype.NonAtomicDomain $ typeRep $ Proxy @Bool)

        it "represents empty datatypes and rejects growing recursive type arguments" $ do
            case Datatype.deriveFTA @EmptyDatatype of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    fmap FTA.cardinality (FTA.fromDatatypeUpToDepth 3 datatype)
                        `shouldBe` Left FTA.EmptyFTALanguage
            void (Datatype.deriveFTA @(Growing Bool))
                `shouldBe` Left (Datatype.NonRegularRecursion (typeRep $ Proxy @(Growing Bool)) (typeRep $ Proxy @(Growing [Bool])))

    describe "ordinary FTA generator syntax" $ do
        it "closes a single do binding as one direct constructor child" $ do
            let boxed = FTA.node "box" $ FTA.do
                    value <- atoms
                    FTA.pure $ value + 1
            FTA.cardinality boxed `shouldBe` 2
            FTA.unrank boxed 1 `shouldBe` Right 2
            FTA.generatedTerm boxed 1
                `shouldBe` Right (Term "box" [Term "one" []])

        it "uses each do binding as one direct constructor child" $ do
            FTA.cardinality pairs `shouldBe` 4
            FTA.generatedTerm pairs 2
                `shouldBe` Right (Term "pair" [Term "one" [], Term "zero" []])

        it "builds exact support carrying the public node labels" $
            case FTA.support pairs of
                Left err -> expectationFailure $ show err
                Right support -> do
                    Automaton.accepts support (Term "pair" [Term "zero" [], Term "one" []])
                        `shouldBe` True
                    Automaton.accepts support (Term "pair" [Term "zero" []])
                        `shouldBe` False

    describe "ordinary FTA compilation" $ do
        it "indexes recursive runs by size and bounds them by depth" $ do
            let rows = [((), [Automaton.Transition "z" [] (), Automaton.Transition "s" [()] ()])]
                terms = take 5 $ iterate (\term -> Term "s" [term]) (Term "z" [])
            case Automaton.mkFTA () rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let check result = case result of
                            Left err -> expectationFailure $ show err
                            Right ranked -> do
                                Ranked.cardinality ranked `shouldBe` 5
                                traverse (Ranked.unrank ranked) [0 .. 4] `shouldBe` Right terms
                                map (Ranked.sizeOfRank ranked) [0 .. 4] `shouldBe` map Just [1 .. 5]
                                Ranked.shrinkRank ranked 4 `shouldSatisfy` (not . null)
                                map (Ranked.unrank ranked) (Ranked.shrinkRank ranked 4)
                                    `shouldSatisfy` all (`elem` map Right (take 4 terms))
                    check $ FTA.fromFTAUpToSize 5 automaton
                    check $ FTA.fromFTAUpToDepth 4 automaton
                    fmap Ranked.cardinality (FTA.fromFTAUpToSize 0 automaton)
                        `shouldBe` Left FTA.EmptyFTALanguage

        it "keeps mutually recursive empty languages and accepting-run ambiguity distinct" $ do
            let rows =
                    [ (0 :: Int, [Automaton.Transition "step" [1] ()])
                    , (1, [Automaton.Transition "again" [0] ()])
                    ]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right empty ->
                    fmap Ranked.cardinality (FTA.fromFTAUpToSize 10 empty)
                        `shouldBe` Left FTA.EmptyFTALanguage
            let productive =
                    (0, [Automaton.Transition "z" [] (), Automaton.Transition "z" [] (), Automaton.Transition "step" [1] ()]) : drop 1 rows
            case Automaton.mkFTA 0 productive of
                Left err -> expectationFailure $ show err
                Right automaton -> case FTA.fromFTAUpToSize 5 automaton of
                    Left err -> expectationFailure $ show err
                    Right ranked -> do
                        Ranked.cardinality ranked `shouldBe` 6
                        let members = map (Ranked.unrank ranked) [0 .. 5]
                        length (nub members) `shouldBe` 3
                        map (Ranked.sizeOfRank ranked) [0 .. 5]
                            `shouldBe` map Just [1, 1, 3, 3, 5, 5]

        it "compiles the common interned unit-constraint graph without ECTA" $ do
            let leaves = Common.Node [Common.Edge "zero" [], Common.Edge "one" []] :: Common.PlainNode String
                root = Common.Node [Common.Edge "pair" [leaves, leaves]]
                expected =
                    [ Term "pair" [Term left [], Term right []]
                    | left <- ["zero", "one"]
                    , right <- ["zero", "one"]
                    ]
            case Common.toFTA root of
                Left err -> expectationFailure $ show err
                Right automaton -> case FTA.fromFTA automaton of
                    Left err -> expectationFailure $ show err
                    Right ranked -> do
                        Ranked.cardinality ranked `shouldBe` 4
                        traverse (Ranked.unrank ranked) [0 .. 3] `shouldBe` Right expected
                        all (Automaton.accepts automaton) expected `shouldBe` True

        it "shares state compilation and decoding across a large finite DAG" $ do
            let depth = 64 :: Int
                rows =
                    (0, [Automaton.Transition "z" [] ()])
                        : [ (state, [Automaton.Transition "a" [state - 1] (), Automaton.Transition "b" [state - 1] ()])
                          | state <- [1 .. depth]
                          ]
                chain symbol = iterate (\term -> Term symbol [term]) (Term "z" []) !! depth
            case Automaton.mkFTA depth rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    completed <- timeout 60000000 $
                        evaluate $
                            case FTA.fromFTA automaton of
                                Left _ -> False
                                Right ranked ->
                                    Ranked.cardinality ranked == 2 ^ depth
                                        && Ranked.unrank ranked 0 == Right (chain "a")
                                        && Ranked.unrank (ranked) (2 ^ depth - 1) == Right (chain "b")
                    completed `shouldBe` Just True

        it "preserves ranks and structural shrinking through shared states" $ do
            let rows =
                    [ (0, [Automaton.Transition "x" [] (), Automaton.Transition "y" [] ()])
                    , (1, [Automaton.Transition "a" [] (), Automaton.Transition "wrap" [0] ()])
                    , (2, [Automaton.Transition "pair" [1, 1] ()])
                    ]
                reference = do
                    leaves <- Ranked.oneof [pure $ Term "x" [], pure $ Term "y" []]
                    alternatives <-
                        Ranked.oneof
                            [ pure $ Term "a" []
                            , pure (\child -> Term "wrap" [child]) <*> leaves
                            ]
                    pure $ pure (\left right -> Term "pair" [left, right]) <*> alternatives <*> alternatives
            case Automaton.mkFTA (2 :: Int) rows of
                Left err -> expectationFailure $ show err
                Right automaton -> case (FTA.fromFTA automaton, reference) of
                    (Right actual, Right expected) -> do
                        let ranks = [0 .. Ranked.cardinality expected - 1]
                        Ranked.cardinality actual `shouldBe` Ranked.cardinality expected
                        map (Ranked.unrank actual) ranks `shouldBe` map (Ranked.unrank expected) ranks
                        map (Ranked.sizeOfRank actual) ranks `shouldBe` map (Ranked.sizeOfRank expected) ranks
                        map (Ranked.shrinkRank actual) ranks `shouldBe` map (Ranked.shrinkRank expected) ranks
                        map (Ranked.smallerMembers actual) ranks `shouldBe` map (Ranked.smallerMembers expected) ranks
                    (Left err, _) -> expectationFailure $ show err
                    (_, Left err) -> expectationFailure $ show err

    describe "ordinary FTA integer expressions" $ do
        it "has the exact structural cardinality at every bounded depth" $
            map (FTA.cardinality . Expressions.expressionsAtDepth) [0 .. 4]
                `shouldBe` map Expressions.expressionCount [0 .. 4]

        it "generates executable expressions without type-side conditions" $ do
            let expressions = Expressions.expressionsAtDepth 2
                generated =
                    [ expression
                    | rank <- [0 .. FTA.cardinality expressions - 1]
                    , Right expression <- [FTA.unrank expressions rank]
                    ]
            length generated `shouldBe` fromInteger (FTA.cardinality expressions)
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
