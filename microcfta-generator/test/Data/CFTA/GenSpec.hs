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
import Data.CFTA.Constraint (noConstraint)
import Data.CFTA.Gen (On ((:==:)))
import Data.CFTA.Gen.Equality.TestSupport (ranksBack, ranksEveryMemberBack)
import qualified Data.CFTA.Gen.Internal.Flat as Flat
import qualified Data.CFTA.Gen.QuickCheck as FTAGen
import qualified Data.CFTA.Gen.UntypedExpressionLanguage as Expressions
import qualified Data.CFTA.Generic as Datatype
import Data.CFTA.Index (Cardinality (..), everyRank)
import qualified Data.CFTA.Interned as Common
import qualified Data.CFTA.Ranked as Ranked
import Data.CFTA.Symbol (Symbol)
import qualified Data.Tree as Tree

-- | A derived recursive fixture with named child positions.
data DerivedTree = Leaf Bool | Fork DerivedTree DerivedTree
    deriving (Eq, Show, Generic)

instance Datatype.HasFTA DerivedTree

{- | A record fixture retains selector names without partial record fields.
| A call with a list of arguments, for a recursion nested in another one.
-}
data Call = NoCall | Call [Call]
    deriving (Eq, Show)

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
                    ranksEveryMemberBack FTAGen.rankOfValue $ FTAGen.fromDatatypeUpToDepth 2 datatype
                    ranksBack FTAGen.rankOfValue (FTAGen.fromDatatype datatype) [0 .. 30]

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
                Right datatype -> do
                    let generator = FTAGen.fromDatatypeUpToDepth 3 datatype
                    traverse (FTAGen.unrank generator) [0 .. 3]
                        `shouldBe` Right [AEnd, AStep BEnd, AStep (BStep AEnd), AStep (BStep (AStep BEnd))]
                    ranksEveryMemberBack FTAGen.rankOfValue generator
                    ranksBack FTAGen.rankOfValue (FTAGen.fromDatatype datatype) [0 .. 5]
            case Datatype.deriveFTA @[[Bool]] of
                Left err -> expectationFailure $ show err
                Right datatype ->
                    Automaton.accepts (Datatype.datatypeFTA datatype) (Datatype.encodeTerm [[True], [], [False]]) `shouldBe` True

        it "requires explicit atomic domains and retains their order without duplicates" $ do
            void (Datatype.deriveFTA @(Maybe Int))
                `shouldBe` Left (Datatype.MissingDomain $ typeRep $ Proxy @Int)
            case Datatype.deriveFTAWith @(Maybe Int) $ Datatype.domain @Int [2, 1, 2] of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    traverse (FTAGen.unrank $ FTAGen.fromDatatypeUpToDepth 1 datatype) [0 .. 2]
                        `shouldBe` Right [Nothing, Just 2, Just 1]
                    ranksEveryMemberBack FTAGen.rankOfValue $ FTAGen.fromDatatypeUpToDepth 1 datatype
            void (Datatype.deriveFTAWith @Bool $ Datatype.domain [False])
                `shouldBe` Left (Datatype.NonAtomicDomain $ typeRep $ Proxy @Bool)

        it "represents empty datatypes and rejects growing recursive type arguments" $ do
            case Datatype.deriveFTA @EmptyDatatype of
                Left err -> expectationFailure $ show err
                Right datatype -> do
                    FTAGen.cardinality (FTAGen.fromDatatypeUpToDepth 3 datatype)
                        `shouldBe` Left FTAGen.EmptyGenerator
                    FTAGen.rankOfTerm (FTAGen.fromDatatypeUpToDepth 3 datatype) (Tree.Node (fromString "EmptyDatatype") [])
                        `shouldBe` Left FTAGen.EmptyGenerator
            void (Datatype.deriveFTA @(Growing Bool))
                `shouldBe` Left
                    ( Datatype.NonRegularRecursion
                        Datatype.defaultGrowthLimit
                        (typeRep $ Proxy @(Growing Bool))
                        (typeRep $ Proxy @(Growing [Bool]))
                    )

    describe "ordinary FTA generator syntax" $ do
        it "reports the error of a failed recursion through joins, groups, and lowering" $ do
            let failed = FTAGen.recur id :: FTAGen.FTAGen String Int
            sampled <- QC.generate (FTAGen.toGenEither failed)
            (sampled, FTAGen.cardinality (FTAGen.match (id :==: id) failed (FTAGen.elements [1 :: Int])))
                `shouldBe` (Left FTAGen.UnguardedRecursion, Left FTAGen.UnguardedRecursion)
            FTAGen.sizes (FTAGen.groupOn id failed) `shouldBe` Left FTAGen.UnguardedRecursion

        it "needs the smaller-member search to remove members before a failing one" $ do
            -- A greedy shrink loop takes the first candidate that still fails.
            -- In a product, structural candidates shrink each component on its
            -- own, so they cannot drop a False in front of the True. A bounded
            -- recursive language shrinks by halving its size-major rank, which
            -- reaches a member with fewer elements here.
            let coin = FTAGen.oneof [FTAGen.leaf False "f", FTAGen.leaf True "t"]
                nested :: Int -> FTAGen.Gen String [Bool]
                nested 0 = FTAGen.leaf [] "nil"
                nested depth = FTAGen.oneof [FTAGen.leaf [] "nil", FTAGen.node "cons" ((:) <$> coin <*> nested (depth - 1))]
                -- [False, False, True] has size seven: three cons nodes, three coins, and nil.
                recursive :: FTAGen.Gen String [Bool]
                recursive =
                    FTAGen.upToSize 7 $
                        FTAGen.recur $
                            \self -> FTAGen.oneof [FTAGen.leaf [] "nil", FTAGen.node "cons" ((:) <$> coin <*> self)]
                shrunk lists withSmaller =
                    let fails rank = either (const False) or (FTAGen.unrank lists rank)
                        candidates rank =
                            (if withSmaller then map FTAGen.valueRank (FTAGen.smallerMembers lists rank) else [])
                                <> FTAGen.shrinkRank lists rank
                        loop rank = case filter fails (candidates rank) of
                            smaller : _ -> loop smaller
                            [] -> rank
                     in case [rank | rank <- [0 .. 62], FTAGen.unrank lists rank == Right [False, False, True]] of
                            start : _ -> FTAGen.unrank lists (loop start)
                            [] -> Left FTAGen.EmptyGenerator
            shrunk (nested 3) False `shouldBe` Right [False, False, True]
            shrunk (nested 3) True `shouldBe` Right [True]
            shrunk recursive False `shouldBe` Right [True]

        it "counts a recursion that reads a tied recursion before its own occurrence" $ do
            let trees :: FTAGen.Gen String DerivedTree
                trees = FTAGen.recur $ \self -> FTAGen.oneof [Leaf <$> FTAGen.elements [False, True], Fork <$> self <*> self]
                forest = FTAGen.recur $ \rest -> FTAGen.oneof [pure [], (:) <$> trees <*> rest]
                -- The constructors Call and (:) pay, which guards the recursions.
                calls :: FTAGen.Gen String Call
                calls =
                    FTAGen.recur $ \self ->
                        FTAGen.oneof
                            [ pure NoCall
                            , FTAGen.pay $ Call <$> FTAGen.recur (\rest -> FTAGen.oneof [pure [], FTAGen.pay $ (:) <$> self <*> rest])
                            ]
                counts = (FTAGen.countAtSize forest 1, map (FTAGen.countAtSize calls) [1 .. 4])
            counted <- timeout 10000000 $ counts <$ evaluate (length $ show counts)
            counted `shouldBe` Just (Right 2, [Right 1, Right 1, Right 2, Right 4])

        it "keeps a nested recursion whose finite members all use the outer occurrence" $ do
            let calls :: FTAGen.Gen String Call
                calls =
                    FTAGen.recur $ \self ->
                        FTAGen.oneof
                            [ pure NoCall
                            , FTAGen.pay $
                                pure Call <*> FTAGen.recur (\rest -> FTAGen.oneof [pure (: []) <*> self, FTAGen.pay $ (:) <$> self <*> rest])
                            ]
            FTAGen.isRecursive calls `shouldBe` True
            map (FTAGen.countAtSize calls) [1 .. 4] `shouldBe` [Right 1, Right 2, Right 5, Right 14]

        it "keeps the outer occurrence through a recursion whose finite members all use the middle occurrence" $ do
            -- The outer recursion reaches its own occurrence only through the
            -- inner recursion. The inner recursion has finite members only
            -- through a product of the middle occurrence and the outer one.
            let pair a b = FTAGen.pay $ (+) <$> a <*> b
                inner m o = FTAGen.recur $ \n -> FTAGen.oneof [pair m o, pair n n]
                middle o = FTAGen.recur $ \m -> FTAGen.oneof [pure 1, inner m o]
                outer :: FTAGen.FTAGen String Int
                outer = FTAGen.recur $ \o -> FTAGen.oneof [pure 0, middle o]
                bounded :: FTAGen.FTAGen String Int
                bounded = FTAGen.recur $ \o -> FTAGen.oneof [pure 0, FTAGen.upToSize 3 $ middle o]
                grouped :: FTAGen.FTAGen String Int
                grouped =
                    FTAGen.recur $ \o ->
                        FTAGen.oneof
                            [ pure 0
                            , FTAGen.atKey () $ FTAGen.recurGrouped $ \m ->
                                FTAGen.keyed () $ FTAGen.oneof [pure 1, inner (FTAGen.atKey () m) o]
                            ]
            -- In each language, O = 0 | M, M = 1 | N, and N = M * O | N * N,
            -- where each product pays one.
            map (FTAGen.countAtSize outer) [0 .. 3] `shouldBe` [Right 2, Right 2, Right 6, Right 26]
            traverse (FTAGen.unrank outer) [0 .. 3] `shouldBe` Right [0, 1, 1, 2]
            map (FTAGen.countAtSize grouped) [0 .. 3] `shouldBe` [Right 2, Right 2, Right 6, Right 26]
            -- A bound around the middle recursion reaches the outer occurrence.
            FTAGen.cardinality bounded `shouldBe` Left FTAGen.BoundedRecursiveOccurrence

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

        it "compiles and walks a language that two alternatives reuse once" $ do
            let depth = 40 :: Int
                chain :: Int -> FTAGen.FTAGen String (Tree.Tree String)
                chain 0 = pure (Tree.Node "z" [])
                chain n = FTAGen.oneof [wrap "a" <$> rest, wrap "b" <$> rest]
                  where
                    rest = chain (n - 1)
                rankedChain :: Int -> Either Ranked.RankedError (Ranked.Ranked (Tree.Tree String))
                rankedChain 0 = Right (pure (Tree.Node "z" []))
                rankedChain n = do
                    rest <- rankedChain (n - 1)
                    Ranked.oneof [wrap "a" <$> rest, wrap "b" <$> rest]
                wrap symbol term = Tree.Node symbol [term]
                path symbol = iterate (wrap symbol) (Tree.Node "z" []) !! depth
                generator = chain depth
                ranked = rankedChain depth
                lastRank = 2 ^ depth - 1
            -- The walks come before the decoders: without shared alternatives
            -- a walk takes exponential time in little memory, and the timeout
            -- stops it before a decoder fills the heap.
            completed <- timeout 10000000 $ do
                drawn <- QC.generate (FTAGen.toGen generator)
                evaluate $
                    FTAGen.minimumSize generator == Right (Just 0)
                        && FTAGen.smallest generator == Right (Just (path "a"))
                        && take 1 (FTAGen.shrinkRank generator lastRank) == [0]
                        && fmap (\language -> take 1 (Ranked.shrinkRank language lastRank)) ranked == Right [0]
                        && length (Tree.flatten drawn) == depth + 1
                        && (ranked >>= (`Ranked.unrank` lastRank)) == Right (path "b")
            completed `shouldBe` Just True

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
            let rows = [((), [Automaton.Transition "z" [] noConstraint, Automaton.Transition "s" [()] noConstraint])]
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
                    -- The terms rank back to their ranks, also by size in the recursive import.
                    let bounded = FTAGen.fromAutomatonUpToDepth 4 node
                        recursive = FTAGen.fromAutomaton node
                        deeper = Tree.Node "s" [last terms]
                        wrongArity = Tree.Node "s" []
                    ranksEveryMemberBack FTAGen.rankOfTerm bounded
                    ranksBack FTAGen.rankOfTerm recursive [0 .. 9]
                    map (FTAGen.rankOfTerm bounded) [deeper, wrongArity]
                        `shouldBe` [Left FTAGen.TermNotInLanguage, Left FTAGen.TermNotInLanguage]
                    map (FTAGen.rankOfTerm recursive) [deeper, wrongArity]
                        `shouldBe` [Right 5, Left FTAGen.TermNotInLanguage]
                    -- The recursive import decodes the term of a size-major rank.
                    traverse (FTAGen.termAt $ FTAGen.fromAutomaton node) [0 .. 4]
                        `shouldBe` Right (map (fmap FTAGen.Label) terms)
                    FTAGen.cardinality (FTAGen.upToSize 0 $ FTAGen.fromAutomaton node)
                        `shouldBe` Left FTAGen.EmptyGenerator

        it "keeps empty recursion distinct from ambiguity and counts distinct finite terms" $ do
            let rows =
                    [ (0 :: Int, [Automaton.Transition "step" [1] noConstraint])
                    , (1, [Automaton.Transition "again" [0] noConstraint])
                    ]
            case Automaton.mkFTA 0 rows of
                Left err -> expectationFailure $ show err
                Right empty -> do
                    FTAGen.cardinality (FTAGen.upToSize 10 $ FTAGen.fromAutomaton $ Common.fromFTA empty)
                        `shouldBe` Left FTAGen.EmptyGenerator
                    FTAGen.rankOfTerm (FTAGen.fromAutomaton $ Common.fromFTA empty) (Tree.Node "step" [Tree.Node "again" []])
                        `shouldBe` Left FTAGen.EmptyGenerator
            let productive =
                    [
                        ( 0 :: Int
                        ,
                            [ Automaton.Transition "z" [] noConstraint
                            , Automaton.Transition "step" [1] noConstraint
                            , Automaton.Transition "step" [2] noConstraint
                            ]
                        )
                    , (1, [Automaton.Transition "again" [0] noConstraint, Automaton.Transition "extra" [] noConstraint])
                    , (2, [Automaton.Transition "again" [0] noConstraint])
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
                    -- The two step alternatives overlap, so the bound ranks symbolically.
                    ranksEveryMemberBack FTAGen.rankOfTerm bounded
                    FTAGen.rankOfTerm (FTAGen.fromAutomaton node) (Tree.Node "z" [])
                        `shouldBe` Left FTAGen.AmbiguousAutomaton

        it "compiles the common interned unit-constraint graph without ECTA" $ do
            let leaves = Common.Node [Common.Edge "zero" [], Common.Edge "one" []] :: Common.Node String
                root = Common.Node [Common.Edge "pair" [leaves, leaves]]
                expected =
                    [ Tree.Node "pair" [Tree.Node left [], Tree.Node right []]
                    | left <- ["one", "zero"]
                    , right <- ["one", "zero"]
                    ]
                generator = FTAGen.fromAutomaton root
            case Common.toFTA root of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    FTAGen.cardinality generator `shouldBe` Right 4
                    traverse (FTAGen.unrank generator) [0 .. 3] `shouldBe` Right expected
                    all (Automaton.accepts automaton) expected `shouldBe` True
                    ranksEveryMemberBack FTAGen.rankOfTerm generator
                    map (FTAGen.rankOfTerm generator) [Tree.Node "pair" [Tree.Node "one" []], Tree.Node "zero" []]
                        `shouldBe` [Left FTAGen.TermNotInLanguage, Left FTAGen.TermNotInLanguage]

        it "ranks imported alternatives in symbol order, not in interning order" $ do
            -- Interning is global: these symbols appear in no other test.
            let leaves = [Tree.Node "order-a" [], Tree.Node "order-b" []]
                flat = Common.Node [Common.Edge "order-a" [], Common.Edge "order-b" []] :: Common.Node String
                transitions =
                    [Automaton.Transition symbol [] noConstraint | symbol <- ["order-b", "order-a"]]
                        <> [Automaton.Transition "order-s" [()] noConstraint]
            -- Intern the later symbol first.
            void $ evaluate $ Common.nodeCount (Common.Node [Common.Edge "order-b" []] :: Common.Node String)
            FTAGen.values (FTAGen.fromAutomaton flat) `shouldBe` Right leaves
            ranksEveryMemberBack FTAGen.rankOfTerm $ FTAGen.fromAutomaton flat
            case Automaton.mkFTA () [((), transitions)] of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    FTAGen.values (FTAGen.upToSize 1 $ FTAGen.fromAutomaton $ Common.fromFTA automaton)
                        `shouldBe` Right leaves
                    ranksBack FTAGen.rankOfTerm (FTAGen.fromAutomaton $ Common.fromFTA automaton) [0 .. 9]

        it "keeps the constructors of one arity apart when the order key does not tell them apart" $ do
            -- Every symbol has the key (), so only the symbol keeps "tie-a" and "tie-b" apart.
            let rows =
                    [ ("q", [Automaton.Transition "tie-f" ["r"] noConstraint, Automaton.Transition "tie-f" ["s"] noConstraint])
                    , ("r", [Automaton.Transition "tie-a" [] noConstraint, Automaton.Transition "tie-b" [] noConstraint])
                    , ("s", [Automaton.Transition "tie-a" [] noConstraint])
                    ]
            case Automaton.mkFTA ("q" :: String) rows of
                Left err -> expectationFailure $ show err
                Right automaton ->
                    FTAGen.values (Flat.fromAutomaton (const ()) $ Common.fromFTA automaton)
                        `shouldBe` Right [Tree.Node "tie-f" [Tree.Node symbol []] | symbol <- ["tie-a", "tie-b"]]

        it "ranks alternatives with one symbol by their children, not in interning order" $ do
            -- Interning is global: these symbols appear in no other test.
            let leaf symbol = Common.Node [Common.Edge symbol []] :: Common.Node String
                pair symbol = Common.Edge "canonical-pair" [leaf symbol]
                flat = Common.Node [pair "canonical-a", pair "canonical-b"]
            -- Intern the later alternative first.
            void $ evaluate $ Common.nodeCount (Common.Node [pair "canonical-b"])
            FTAGen.values (FTAGen.fromAutomaton flat)
                `shouldBe` Right [Tree.Node "canonical-pair" [Tree.Node symbol []] | symbol <- ["canonical-a", "canonical-b"]]
            ranksEveryMemberBack FTAGen.rankOfTerm $ FTAGen.fromAutomaton flat

        it "ranks alternatives with one symbol in a cyclic automaton by their children" $ do
            -- Interning is global: these symbols appear in no other test.
            let leaf symbol = Common.Node [Common.Edge symbol []] :: Common.Node String
                pair symbol = Common.Edge "cyclic-pair" [leaf symbol]
                cyclic = Common.createMu $ \self -> Common.Node [Common.Edge "cyclic-end" [], Common.Edge "cyclic-wrap" [self], pair "cyclic-a", pair "cyclic-b"]
                paired symbol = Tree.Node "cyclic-pair" [Tree.Node symbol []]
            -- Intern the later alternative first.
            void $ evaluate $ Common.nodeCount (Common.Node [pair "cyclic-b"])
            FTAGen.values (FTAGen.upToSize 2 $ FTAGen.fromAutomaton cyclic)
                `shouldBe` Right
                    [ Tree.Node "cyclic-end" []
                    , paired "cyclic-a"
                    , paired "cyclic-b"
                    , Tree.Node "cyclic-wrap" [Tree.Node "cyclic-end" []]
                    ]

        it "shares state compilation and decoding across a large finite DAG" $ do
            let depth = 64 :: Int
                rows =
                    (0, [Automaton.Transition "z" [] noConstraint])
                        : [ (state, [Automaton.Transition "a" [state - 1] noConstraint, Automaton.Transition "b" [state - 1] noConstraint])
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
                    -- The size and shrink walks read each shared state once.
                    walked <-
                        timeout 60000000
                            $ evaluate
                            $ FTAGen.minimumSize generator == Right (Just (toEnum depth + 1))
                                && FTAGen.smallest generator == Right (Just (chain "a"))
                                && null (FTAGen.smallerMembers generator 0)
                                && take 1 (FTAGen.shrinkRank generator (2 ^ depth - 1)) == [0]
                    walked `shouldBe` Just True
                    ranksBack FTAGen.rankOfTerm generator [0, 1, 2 ^ (depth - 1), 2 ^ depth - 1]

        it "preserves ranks and structural shrinking through shared states" $ do
            let rows =
                    [ (0, [Automaton.Transition "x" [] noConstraint, Automaton.Transition "y" [] noConstraint])
                    , (1, [Automaton.Transition "a" [] noConstraint, Automaton.Transition "wrap" [0] noConstraint])
                    , (2, [Automaton.Transition "pair" [1, 1] noConstraint])
                    ]
                -- Each node of an imported term pays one, so each node of the reference pays.
                reference = do
                    leaves <- Ranked.oneof [Ranked.pay $ pure $ Tree.Node "x" [], Ranked.pay $ pure $ Tree.Node "y" []]
                    alternatives <-
                        Ranked.oneof
                            [ Ranked.pay $ pure $ Tree.Node "a" []
                            , Ranked.pay $ pure (\child -> Tree.Node "wrap" [child]) <*> leaves
                            ]
                    pure $ Ranked.pay $ pure (\left right -> Tree.Node "pair" [left, right]) <*> alternatives <*> alternatives
            case Automaton.mkFTA (2 :: Int) rows of
                Left err -> expectationFailure $ show err
                Right automaton -> case reference of
                    Left err -> expectationFailure $ show err
                    Right expected -> do
                        let actual = FTAGen.fromAutomaton $ Common.fromFTA automaton
                            ranks = everyRank $ Ranked.cardinality expected
                            members = either (const Nothing) Just
                        FTAGen.cardinality actual `shouldBe` Right (Ranked.cardinality expected)
                        members (traverse (FTAGen.unrank actual) ranks) `shouldBe` members (traverse (Ranked.unrank expected) ranks)
                        map (FTAGen.sizeOfRank actual) ranks `shouldBe` map (Ranked.sizeOfRank expected) ranks
                        map (FTAGen.shrinkRank actual) ranks `shouldBe` map (Ranked.shrinkRank expected) ranks
                        map (FTAGen.smallerMembers actual) ranks `shouldBe` map (Ranked.smallerMembers expected) ranks
                        ranksEveryMemberBack FTAGen.rankOfTerm actual

        it "positions left-deep terms of transitions that share a symbol" $ do
            -- Both f transitions accept every left child, and only the right
            -- child tells them apart. A search from the root would visit the
            -- left child once for each transition at each level.
            let rows =
                    [
                        ( "list"
                        ,
                            [ Automaton.Transition "a" [] noConstraint
                            , Automaton.Transition "f" ["list", "b"] noConstraint
                            , Automaton.Transition "f" ["list", "c"] noConstraint
                            ]
                        )
                    , ("b", [Automaton.Transition "b" [] noConstraint])
                    , ("c", [Automaton.Transition "c" [] noConstraint])
                    ]
                deep = foldl' (\term right -> Tree.Node "f" [term, Tree.Node right []]) (Tree.Node "a" []) (replicate 40 "c")
            case Automaton.mkFTA "list" rows of
                Left err -> expectationFailure $ show err
                Right automaton -> do
                    let generator = FTAGen.fromAutomaton $ Common.fromFTA automaton
                    ranksBack FTAGen.rankOfTerm generator [0 .. 30]
                    FTAGen.rankOfTerm generator (Tree.Node "f" [Tree.Node "a" [], Tree.Node "a" []])
                        `shouldBe` Left FTAGen.TermNotInLanguage
                    (FTAGen.rankOfTerm generator deep >>= \rank -> (,) (FTAGen.sizeOfRank generator rank) <$> FTAGen.unrank generator rank)
                        `shouldBe` Right (Just 81, deep)

    describe "ordinary FTA integer expressions" $ do
        it "has the exact structural cardinality at every bounded depth" $
            map (FTAGen.cardinality . Expressions.expressionsAtDepth) [0 .. 4]
                `shouldBe` map (Right . Cardinality . Expressions.expressionCount) [0 .. 4]

        it "generates executable expressions without type-side conditions" $ do
            let expressions = Expressions.expressionsAtDepth 2
                total = fromRight 0 $ FTAGen.cardinality expressions
                generated =
                    [ expression
                    | rank <- everyRank total
                    , Right expression <- [FTAGen.unrank expressions rank]
                    ]
            toEnum (length generated) `shouldBe` total
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
acceptsPlain :: Common.Node (FTAGen.Label String) -> Tree.Tree (FTAGen.Label String) -> Bool
acceptsPlain = Common.acceptsWith (\_ _ -> True)

-- | The generator symbol of a derived constructor.
constructorSymbol :: Datatype.Constructor -> FTAGen.Label Symbol
constructorSymbol = FTAGen.Label . fromString . Datatype.constructorLabel
