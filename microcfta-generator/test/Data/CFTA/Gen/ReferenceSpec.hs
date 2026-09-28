{- | Differential tests: the engine against the reference model of
"Data.CFTA.Gen.Reference", on random descriptions.
-}
module Data.CFTA.Gen.ReferenceSpec (spec) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import qualified Data.Text as Text
import Test.Hspec (Spec, describe, it)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import Test.QuickCheck (Property, counterexample, (.&&.), (===))
import qualified Test.QuickCheck as QC

import Data.CFTA.Equality (numNestedMu, plainTermsAtMost, terms)
import Data.CFTA.Gen (GenError (..))
import qualified Data.CFTA.Gen as Gen
import Data.CFTA.Gen.Reference
import Data.CFTA.Index (Cardinality (..), Rank, Size (..), everyRank)
import Data.CFTA.Ranked.Internal.Sampler (Exact (..))

-- | A closed random description.
newtype Closed = Closed Desc
    deriving (Show)

instance QC.Arbitrary Closed where
    arbitrary = Closed <$> QC.sized (\budget -> description 0 0 $ min 14 budget)
    shrink (Closed desc) = [Closed smaller | smaller <- shrinkDesc desc, closed smaller]

-- | A closed random grouped description.
newtype ClosedFamily = ClosedFamily GDesc
    deriving (Show)

instance QC.Arbitrary ClosedFamily where
    arbitrary = ClosedFamily <$> QC.sized (\budget -> family 0 0 $ min 14 budget)
    shrink (ClosedFamily desc) = [ClosedFamily smaller | smaller <- shrinkFamily desc, closedGrouped smaller]

{- | A random description inside the given numbers of recursions and grouped
recursions, of about the given number of constructors.
-}
description :: Int -> Int -> Int -> QC.Gen Desc
description depth grouped budget
    | budget <= 1 = leaf
    | otherwise =
        QC.frequency
            [ (2, leaf)
            , (2, Node <$> QC.elements (map Text.pack ["a", "b"]) <*> inner)
            , (1, Tag <$> QC.chooseInt (0, 2) <*> inner)
            , (4, Pair <$> half <*> half)
            , (3, Frequency <$> alternatives)
            , (1, Uniformly . map snd <$> alternatives)
            , (1, Atomic <$> bounded)
            , (2, UpToSize <$> QC.chooseInt (0, 5) <*> bounded)
            , (if depth < 2 then 1 else 0, Recur <$> description (depth + 1) grouped (budget - 1))
            , (if depth < 2 then 4 else 0, productive)
            , (if depth == 0 then 2 else 0, crossing)
            , (1, AtKey <$> QC.chooseInt (0, 2) <*> family depth grouped (budget - 1))
            , (1, Ungroup <$> family depth grouped (budget - 1))
            , (1, Match <$> QC.chooseInt (1, 3) <*> half <*> half)
            , (1, Relate <$> QC.chooseInt (1, 3) <*> half <*> half)
            ]
  where
    leaf =
        QC.frequency $
            [ (3, Pure <$> QC.chooseInt (0, 3))
            , (2, Elements <$> QC.frequency [(1, pure []), (12, QC.chooseInt (1, 3) >>= (`QC.vectorOf` QC.chooseInt (0, 3)))])
            ]
                <> [(1, Var <$> QC.chooseInt (0, depth - 1)) | depth > 0]
    inner = description depth grouped (budget - 1)
    half = description depth grouped (budget `div` 2)
    -- Mostly a closed language: a bound around an occurrence is an error. A
    -- bound around three nested recursions can keep tens of thousands of
    -- members, and a join reads each of them, so a bound has fewer.
    bounded = QC.frequency [(6, description 0 0 (budget - 1)), (1, inner)] `QC.suchThat` ((< 3) . recursionDepth)
    alternatives = weighted (description depth grouped) budget
    -- A recursion with a base case and an occurrence under a product.
    productive = do
        base <- description (depth + 1) grouped (budget `div` 3)
        other <- description (depth + 1) grouped (budget `div` 3)
        weight <- QC.frequency [(8, pure 1), (1, pure 2)]
        occurrenceLeft <- QC.arbitrary
        let product' = if occurrenceLeft then Pair (Var 0) other else Pair other (Var 0)
        pure $ Recur $ Frequency [(1, base), (weight, product')]
    -- Three nested recursions. The finite members of the innermost one all go
    -- through a product of the middle occurrence and the outer occurrence, so
    -- the innermost recursion is empty unless the middle occurrence has a
    -- member. The middle level is a recursion or a recursive family.
    crossing = do
        outerBase <- description 1 grouped (budget `div` 3)
        middleLeft <- QC.arbitrary
        let across first second = if middleLeft then Pair first second else Pair second first
        middle <-
            QC.oneof
                [ do
                    middleBase <- description 2 grouped (budget `div` 3)
                    other <- description 3 grouped (budget `div` 3)
                    let innermost = Recur $ Frequency [(1, across (Var 1) (Var 2)), (1, Pair (Var 0) other)]
                    pure $ Recur $ Frequency [(1, middleBase), (1, innermost)]
                , do
                    key <- QC.chooseInt (0, 2)
                    middleBase <- description 1 (grouped + 1) (budget `div` 3)
                    other <- description 2 (grouped + 1) (budget `div` 3)
                    let innermost =
                            Recur $ Frequency [(1, across (AtKey key (GVar 0)) (Var 1)), (1, Pair (Var 0) other)]
                    pure $ AtKey key $ RecurGrouped $ Keyed key $ Frequency [(1, middleBase), (1, innermost)]
                ]
        pure $ Recur $ Frequency [(1, outerBase), (1, middle)]

-- | A random grouped description, as 'description' gives an ordinary one.
family :: Int -> Int -> Int -> QC.Gen GDesc
family depth grouped budget
    | budget <= 1 = leaf
    | otherwise =
        QC.frequency
            [ (3, leaf)
            , (2, Regroup <$> QC.chooseInt (1, 3) <*> inner)
            , (1, MapWithKey <$> inner)
            , (2, Frequencies <$> weighted (family depth grouped) budget)
            , (3, Apply1 <$> operations ((,,) <$> key <*> key) <*> inner)
            , (2, Apply2 <$> operations ((,,,) <$> key <*> key <*> key) <*> half <*> half)
            , (if grouped < 2 then 1 else 0, RecurGrouped <$> family depth (grouped + 1) (budget - 1))
            , (if grouped < 2 then 3 else 0, productive)
            ]
  where
    leaf =
        QC.frequency $
            [ (3, Keyed <$> key <*> description depth grouped (budget `div` 2))
            , (4, GroupOn <$> QC.chooseInt (2, 3) <*> description depth grouped (budget `div` 2))
            ]
                <> [(2, GVar <$> QC.chooseInt (0, grouped - 1)) | grouped > 0]
    key = QC.chooseInt (0, 2)
    inner = family depth grouped (budget - 1)
    half = family depth grouped (budget `div` 2)
    operations :: QC.Gen (Desc -> operation) -> QC.Gen [operation]
    operations keys = do
        count <- QC.chooseInt (1, 3)
        QC.vectorOf count $ keys <*> operation
    -- Mostly a source: a recursive operation makes the operation family recursive.
    operation =
        QC.frequency
            [ (5, Pure <$> QC.chooseInt (0, 3))
            , (5, Elements <$> (QC.chooseInt (1, 3) >>= (`QC.vectorOf` QC.chooseInt (0, 3))))
            , (2, description 0 0 (budget `div` 4))
            , (1, description depth grouped (budget `div` 4))
            ]
    -- A grouped recursion with a keyed base case and an application to the family.
    productive = do
        base <- Keyed <$> key <*> description depth (grouped + 1) (budget `div` 3)
        count <- QC.chooseInt (1, 3)
        steps <- QC.vectorOf count $ (,,) <$> key <*> key <*> operation
        pure $ RecurGrouped $ Frequencies [(1, base), (1, Apply1 steps (GVar 0))]

-- | Weighted alternatives, mostly with equal weights: unequal weights around a recursive alternative are an error.
weighted :: (Int -> QC.Gen a) -> Int -> QC.Gen [(Integer, a)]
weighted alternative budget = do
    count <- QC.chooseInt (1, 3)
    weights <-
        QC.frequency
            [ (16, pure $ replicate count 1)
            , (6, QC.vectorOf count $ QC.chooseInteger (1, 3))
            , (1, QC.vectorOf count $ QC.chooseInteger (0, 2))
            ]
    zip weights <$> QC.vectorOf count (alternative $ budget `div` count)

-- | The largest number of recursions, ordinary and grouped, that enclose one another in a description.
recursionDepth :: Desc -> Int
recursionDepth = \case
    Pure _ -> 0
    Elements _ -> 0
    Node _ inner -> recursionDepth inner
    Tag _ inner -> recursionDepth inner
    Pair left right -> max (recursionDepth left) (recursionDepth right)
    Frequency alternatives -> maximum $ 0 : map (recursionDepth . snd) alternatives
    Uniformly alternatives -> maximum $ 0 : map recursionDepth alternatives
    Atomic inner -> recursionDepth inner
    UpToSize _ inner -> recursionDepth inner
    Recur body -> 1 + recursionDepth body
    Var _ -> 0
    AtKey _ family' -> familyDepth family'
    Ungroup family' -> familyDepth family'
    Match _ left right -> max (recursionDepth left) (recursionDepth right)
    Relate _ left right -> max (recursionDepth left) (recursionDepth right)
  where
    familyDepth = \case
        Keyed _ inner -> recursionDepth inner
        GroupOn _ inner -> recursionDepth inner
        Regroup _ family' -> familyDepth family'
        MapWithKey family' -> familyDepth family'
        Frequencies alternatives -> maximum $ 0 : map (familyDepth . snd) alternatives
        Apply1 operations argument -> maximum $ familyDepth argument : [recursionDepth operation | (_, _, operation) <- operations]
        Apply2 operations first second ->
            maximum $ familyDepth first : familyDepth second : [recursionDepth operation | (_, _, _, operation) <- operations]
        RecurGrouped body -> 1 + familyDepth body
        GVar _ -> 0

-- | Smaller descriptions: the direct parts first, then each part made smaller.
shrinkDesc :: Desc -> [Desc]
shrinkDesc = \case
    Pure n -> [Pure 0 | n /= 0]
    Elements ns -> map Elements $ QC.shrinkList (const []) ns
    Node symbol inner -> inner : map (Node symbol) (shrinkDesc inner)
    Tag n inner -> inner : map (Tag n) (shrinkDesc inner)
    Pair left right ->
        [left, right]
            <> [Pair smaller right | smaller <- shrinkDesc left]
            <> [Pair left smaller | smaller <- shrinkDesc right]
    Frequency alternatives ->
        map snd alternatives
            <> map Frequency (QC.shrinkList (shrinkWeighted shrinkDesc) alternatives)
    Uniformly alternatives -> alternatives <> map Uniformly (QC.shrinkList shrinkDesc alternatives)
    Atomic inner -> inner : map Atomic (shrinkDesc inner)
    UpToSize bound inner ->
        inner
            : [UpToSize smaller inner | smaller <- QC.shrink bound]
                <> map (UpToSize bound) (shrinkDesc inner)
    Recur body -> body : map Recur (shrinkDesc body)
    Var _ -> []
    AtKey key family' -> [AtKey smaller family' | smaller <- QC.shrink key] <> map (AtKey key) (shrinkFamily family')
    Ungroup family' -> map Ungroup $ shrinkFamily family'
    Match n left right ->
        [left, right]
            <> [Match n smaller right | smaller <- shrinkDesc left]
            <> [Match n left smaller | smaller <- shrinkDesc right]
    Relate n left right ->
        [Match n left right, left, right]
            <> [Relate n smaller right | smaller <- shrinkDesc left]
            <> [Relate n left smaller | smaller <- shrinkDesc right]

-- | Smaller grouped descriptions, as 'shrinkDesc' gives.
shrinkFamily :: GDesc -> [GDesc]
shrinkFamily = \case
    Keyed key inner -> [Keyed smaller inner | smaller <- QC.shrink key] <> map (Keyed key) (shrinkDesc inner)
    GroupOn n inner -> [Keyed 0 inner] <> map (GroupOn n) (shrinkDesc inner)
    Regroup n family' -> family' : map (Regroup n) (shrinkFamily family')
    MapWithKey family' -> family' : map MapWithKey (shrinkFamily family')
    Frequencies alternatives ->
        map snd alternatives
            <> map Frequencies (QC.shrinkList (shrinkWeighted shrinkFamily) alternatives)
    Apply1 operations argument ->
        argument
            : [Apply1 smaller argument | smaller <- QC.shrinkList shrinkOperation operations, not $ null smaller]
                <> map (Apply1 operations) (shrinkFamily argument)
    Apply2 operations first second ->
        [first, second]
            <> [Apply2 operations smaller second | smaller <- shrinkFamily first]
            <> [Apply2 operations first smaller | smaller <- shrinkFamily second]
    RecurGrouped body -> body : map RecurGrouped (shrinkFamily body)
    GVar _ -> []
  where
    shrinkOperation (argumentKey, resultKey, operation) =
        [(argumentKey, resultKey, smaller) | smaller <- shrinkDesc operation]

shrinkWeighted :: (a -> [a]) -> (Integer, a) -> [(Integer, a)]
shrinkWeighted shrinkOne (weight, alternative) =
    [(1, alternative) | weight /= 1] <> [(weight, smaller) | smaller <- shrinkOne alternative]

{- | A closed random automaton: acyclic, or recursive and unambiguous, with a
different symbol for each alternative of a node and no equalities.
-}
newtype RandomAutomaton = RandomAutomaton Automaton
    deriving (Show)

instance QC.Arbitrary RandomAutomaton where
    arbitrary = RandomAutomaton <$> QC.oneof [acyclic 2, Loop <$> unambiguous 1 2]
    shrink (RandomAutomaton automaton) =
        [RandomAutomaton smaller | smaller <- shrinkAutomaton automaton, closedAutomaton smaller]

-- | The symbols of the automata and their arities.
symbolArities :: [(Text.Text, Int)]
symbolArities = [(Text.pack symbol, arity) | (symbol, arity) <- [("a", 0), ("b", 0), ("f", 1), ("g", 2), ("h", 2)]]

-- | An acyclic automaton of at most the given depth. Alternatives can overlap, and a binary alternative can require equal children.
acyclic :: Int -> QC.Gen Automaton
acyclic depth = do
    count <- QC.frequency [(1, pure 0), (8, QC.chooseInt (1, 3))]
    States <$> QC.vectorOf count edge
  where
    edge = do
        (symbol, arity) <- QC.elements [entry | entry@(_, arity) <- symbolArities, depth > 0 || arity == 0]
        children <- QC.vectorOf arity $ acyclic (depth - 1)
        equal <- if arity == 2 then QC.frequency [(3, pure False), (1, pure True)] else pure False
        pure $ AutomatonEdge symbol children equal

{- | A node inside the given number of loops, with a nullary alternative and a
different symbol for each alternative. A child is an enclosing loop, a node,
or a nested loop, and a leaf once the budget of nested nodes is spent.
-}
unambiguous :: Int -> Int -> QC.Gen Automaton
unambiguous loops budget = do
    base <- QC.elements [symbol | (symbol, 0) <- symbolArities]
    others <- QC.sublistOf [entry | entry@(symbol, _) <- symbolArities, symbol /= base]
    States <$> traverse edge ((base, 0) : others)
  where
    edge (symbol, arity) = do
        children <- QC.vectorOf arity child
        pure $ AutomatonEdge symbol children False
    child
        | budget <= 0 = QC.frequency [(3, Back <$> QC.chooseInt (0, loops - 1)), (1, leaf)]
        | otherwise =
            QC.frequency
                [ (3, Back <$> QC.chooseInt (0, loops - 1))
                , (2, unambiguous loops (budget - 1))
                , (1, Loop <$> unambiguous (loops + 1) (budget - 1))
                ]
    leaf = do
        symbol <- QC.elements [symbol | (symbol, 0) <- symbolArities]
        pure $ States [AutomatonEdge symbol [] False]

shrinkAutomaton :: Automaton -> [Automaton]
shrinkAutomaton = \case
    States edges ->
        [child | AutomatonEdge _ children _ <- edges, child <- children]
            <> map States (QC.shrinkList shrinkEdge edges)
    Loop body -> body : map Loop (shrinkAutomaton body)
    Back _ -> []
  where
    shrinkEdge (AutomatonEdge symbol children equal) =
        [AutomatonEdge symbol children False | equal]
            <> [ AutomatonEdge symbol (before <> [smaller] <> after) equal
               | (before, current : after) <- map (`splitAt` children) [0 .. length children - 1]
               , smaller <- shrinkAutomaton current
               ]

{- | An imported automaton gives every term that the core lists, once: the
count, the values, and the term of each rank. A recursive import counts
by size, the number of term nodes, and ranks by size first.
-}
importAgreement :: RandomAutomaton -> Property
importAgreement (RandomAutomaton automaton) =
    counterexample (show automaton)
        $ QC.within 5000000
        $ if numNestedMu node == 0
            then finiteAgreement (Gen.fromAutomaton node) (terms node)
            else
                QC.conjoin $
                    recursiveAgreement
                        : [ counterexample ("depth " <> show depth) $
                                finiteAgreement (Gen.fromAutomatonUpToDepth depth node) (plainTermsAtMost depth node)
                          | depth <- [0 .. 2]
                          ]
  where
    node = automatonNode automaton
    finiteAgreement generator found
        | null found = Gen.cardinality generator === Left EmptyGenerator
        | otherwise =
            QC.conjoin $
                (Gen.cardinality generator === Right (Cardinality total))
                    : [fmap sort (Gen.values generator) === Right (sort found) | total <= listBound]
                        <> [ counterexample ("rank " <> show rank) $ case Gen.unrank generator rank of
                                Left err -> counterexample (show err) False
                                Right term -> counterexample (show term) $ term `elem` found
                           | rank <- take rankBound $ everyRank $ Cardinality total
                           ]
      where
        total = toInteger $ length found
    recursiveGenerator = Gen.fromAutomaton node
    recursiveAgreement =
        QC.conjoin $
            (Gen.isRecursive recursiveGenerator === True)
                : [ counterexample ("size " <> show size) $
                        Gen.countAtSize recursiveGenerator (Size size) === Right (toEnum $ length $ termsOfSize automaton size)
                  | size <- [1 .. sizeBound]
                  ]
                    <> [ counterexample ("rank " <> show rank) $ case Gen.unrank recursiveGenerator rank of
                            Left err -> counterexample (show err) False
                            Right term ->
                                Gen.sizeOfRank recursiveGenerator rank === Just (Size size)
                                    .&&. term `elem` termsOfSize automaton size
                              where
                                size = toInteger $ length term
                       | rank <- take rankBound [0 ..]
                       , maybe False (<= Size sizeBound) $ Gen.sizeOfRank recursiveGenerator rank
                       ]

-- | The largest size that a property reads.
sizeBound :: Integer
sizeBound = 7

-- | The number of ranks that a property reads.
rankBound :: Int
rankBound = 48

-- | The largest language whose members a property lists in full.
listBound :: Integer
listBound = 256

-- | A property of one described generator and its model, with a time limit.
agreement :: (Gen.Gen Text.Text Value -> Lang Value -> Property) -> Closed -> Property
agreement check (Closed desc) =
    counterexample (show desc)
        $ QC.tabulate "language" [kind]
        $ QC.within 5000000
        $ check (build desc) lang
  where
    lang = model desc
    kind = case langModel lang of
        Left err -> "error " <> takeWhile (/= ' ') (show err)
        Right Model{modelFinite = Just (total, _)} -> "finite, " <> magnitude total <> " members"
        Right Model{modelFinite = Nothing} -> "recursive"
    magnitude total
        | total <= 1 = "1"
        | total <= 10 = "2-10"
        | total <= 100 = "11-100"
        | otherwise = "over 100"

spec :: Spec
spec = describe "the engine against the reference model" $ modifyMaxSuccess (const 400) $ do
    it "gives the kind, the error, and the counts by size of the model" $ QC.property $ agreement $ \generator lang ->
        case langModel lang of
            Left err ->
                Gen.cardinality generator === Left err
                    .&&. Gen.isRecursive generator === langRecursive lang
            Right model' ->
                QC.conjoin $
                    [ Gen.isRecursive generator === langRecursive lang
                    , Gen.cardinality generator === maybe (Left UnboundedGenerator) (Right . Cardinality . fst) (modelFinite model')
                    , Gen.minimumSize generator === Right (Size <$> modelMinimum model')
                    ]
                        <> [ counterexample ("size " <> show size) $
                                Gen.countAtSize generator (Size size) === Right (Cardinality $ modelCount model' size)
                           | size <- [1 .. sizeBound]
                           ]

    it "decodes each rank to the member and the size of the model" $ QC.property $ agreement $ \generator lang ->
        QC.conjoin $
            [ counterexample ("rank " <> show rank) $
                Gen.unrank generator rank === Right value
                    .&&. Gen.sizeOfRank generator rank === Just (Size size)
            | (rank, (value, size)) <- zip [0 ..] $ take rankBound $ members sizeBound lang
            ]
                <> case langModel lang of
                    Right Model{modelFinite = Just (total, finite)}
                        | total <= listBound ->
                            [ Gen.values generator === Right (map memberValue finite)
                            , Gen.smallest generator === Right (Just $ memberValue $ smallestMember finite)
                            ]
                    Right model'@Model{modelFinite = Nothing} ->
                        [ Gen.smallest generator
                            === Right (fst <$> (listToMaybe . modelClass model' =<< modelMinimum model'))
                        ]
                    _ -> []

    it "gives the distribution of the model" $ QC.property $ agreement $ \generator lang -> case langModel lang of
        Right Model{modelFinite = Just (total, finite)}
            | total <= listBound ->
                QC.conjoin $
                    [ Gen.pmf generator === Right (aggregate [(memberValue member, memberMass member) | member <- finite])
                    , sampledRanks generator === Map.fromList (zip [0 ..] $ map memberMass finite)
                    ]
                        <> [ counterexample ("size " <> show size) $
                                Gen.pmfAtSize generator (Size size) === Right (conditional size finite)
                           | size <- [1 .. sizeBound]
                           ]
        Right model'@Model{modelFinite = Nothing} ->
            QC.conjoin $
                (Gen.pmf generator === Left UnboundedGenerator)
                    : [ counterexample ("size " <> show size) $
                            Gen.pmfAtSize generator (Size size) === Right (aggregate $ modelClass model' size)
                      | size <- [1 .. sizeBound]
                      , modelCount model' size <= listBound
                      ]
        _ -> QC.property True

    it "shrinks to smaller ranks of members no larger" $ QC.property $ agreement $ \generator lang -> case langModel lang of
        Right Model{modelFinite = Just (total, finite)} ->
            let sizes = Map.fromList $ zip [0 ..] $ map memberSize $ take rankBound finite
             in QC.conjoin $
                    [ counterexample ("rank " <> show rank <> ", candidate " <> show candidate) $
                        candidate >= 0 && candidate < rank && Map.lookup candidate sizes <= Just size
                    | (rank, size) <- Map.toList sizes
                    , candidate <- Gen.shrinkRank generator rank
                    ]
                        <> [ counterexample ("rank " <> show rank) $ smallerAgree generator finite rank
                           | total <= listBound
                           , rank <- take rankBound $ everyRank $ Cardinality total
                           ]
        Right Model{modelFinite = Nothing} ->
            let listed = zip [0 ..] $ take rankBound $ members sizeBound lang
             in QC.conjoin
                    [ counterexample ("rank " <> show rank) $
                        Gen.shrinkRank generator rank === []
                            .&&. Gen.smallerMembers generator rank
                                === [Gen.RankedValue smaller value | (smaller, (value, smallerSize)) <- listed, smallerSize < size]
                    | (rank, (_, size)) <- listed
                    ]
        _ -> QC.property True

    it "gives the sizes, the counts, and the key masses of a grouped model" $ QC.property familyAgreement

    it "imports every term of an automaton once" $ QC.property importAgreement

-- | The grouped observers of one described family agree with its model.
familyAgreement :: ClosedFamily -> Property
familyAgreement (ClosedFamily desc) =
    counterexample (show desc)
        $ QC.tabulate "family" [kind]
        $ QC.within 5000000
        $ QC.conjoin
        $ (Gen.sizes grouped === expectedSizes)
            : [ counterexample ("size " <> show size) $
                    Gen.countsAtSize grouped (Size size) === expectedCounts size
                        .&&. Gen.massesAtSize grouped (Size size) === expectedMasses size
              | size <- [0 .. sizeBound]
              ]
  where
    grouped = buildGrouped desc
    family' = modelGrouped desc
    kind = case familyGroups family' of
        Left err -> "error " <> takeWhile (/= ' ') (show err)
        Right groups -> (if familyRecursive family' then "recursive, " else "finite, ") <> show (Map.size groups) <> " keys"
    expectedSizes
        | familyRecursive family' = familyGroups family' >> Left UnboundedGenerator
        | otherwise = fmap (maybe 0 (Cardinality . fst) . modelFinite . groupModel) <$> familyGroups family'
    expectedCounts size = do
        groups <- familyGroups family'
        pure $
            if size < 1
                then Map.empty
                else Map.filter (> 0) $ fmap (\group -> Cardinality $ modelCount (groupModel group) size) groups
    expectedMasses size = do
        groups <- familyGroups family'
        let positive = Map.filter (> 0) $ fmap (massAt size) groups
            total = sum positive
        pure $ if size < 1 || total <= 0 then Map.empty else fmap (/ total) positive
    massAt size group
        | familyRecursive family' = groupMassAt group size
        | otherwise =
            groupMass group
                * sum [memberMass member | member <- maybe [] snd $ modelFinite $ groupModel group, memberSize member == size]

-- | The first member of least size.
smallestMember :: [Member Value] -> Member Value
smallestMember = foldr1 (\member best -> if memberSize member <= memberSize best then member else best)

-- | Sum the masses of equal values, in value order.
aggregate :: [(Value, Rational)] -> [(Value, Rational)]
aggregate = Map.toAscList . Map.fromListWith (+)

-- | The distribution of a finite language conditional on one size.
conditional :: Integer -> [Member Value] -> [(Value, Rational)]
conditional size finite
    | total == 0 = []
    | otherwise = aggregate [(memberValue member, memberMass member / total) | member <- selected]
  where
    selected = filter ((== size) . memberSize) finite
    total = sum $ map memberMass selected

-- | The exact mass of each sampled rank; a sample whose value is not the value of its rank is an error.
sampledRanks :: Gen.Gen Text.Text Value -> Map.Map Rank Rational
sampledRanks generator =
    Map.fromListWith
        (+)
        [ (rank, mass)
        | (mass, sample) <- runExact $ Gen.lowerWithRankVia generator
        , Gen.RankedValue rank value <- either (error . ("sample failed: " <>) . show) pure sample
        , Gen.unrank generator rank == Right value || error ("sampled rank " <> show rank <> " with another value")
        ]

-- | The smaller members of one finite rank: every member of smaller size, in size order, with its value.
smallerAgree :: Gen.Gen Text.Text Value -> [Member Value] -> Rank -> Property
smallerAgree generator finite rank =
    counterexample ("listed " <> show listed) $
        sort (map Gen.valueRank listed) === [smaller | (smaller, member) <- ranked, memberSize member < size]
            .&&. listedSizes === sort listedSizes
            .&&. and [(memberValue <$> lookup smaller ranked) == Just value | Gen.RankedValue smaller value <- listed]
  where
    ranked = zip [0 ..] finite
    size = maybe 0 memberSize $ lookup rank ranked
    listed = Gen.smallerMembers generator rank
    listedSizes = [maybe 0 memberSize $ lookup smaller ranked | Gen.RankedValue smaller _ <- listed]
