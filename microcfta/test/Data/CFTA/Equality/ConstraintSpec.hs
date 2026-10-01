module Data.CFTA.Equality.ConstraintSpec (spec) where

import qualified Data.IntMap.Lazy as IntMap
import Data.List (nub, sort, subsequences, (\\))
import qualified Data.Set as Set
import qualified Data.Tree as Tree

import Test.Hspec
import Test.QuickCheck

import Data.CFTA.Constraint (equalitiesHold, equalityConstraint)
import Data.CFTA.Equality.Constraint
import Data.CFTA.Path

-----------------------------------------------------------------

-----------------------------------
------ PathTrie testing utils
-----------------------------------

-----------------------------------
------ Random generation
-----------------------------------

instance Arbitrary Path where
    arbitrary = path <$> listOf (chooseInt (0, 4))
    shrink = map Path . shrink . unPath

instance Arbitrary PathTrie where
    arbitrary = do
        paths <- suchThat arbitrary (\ps -> not (isContradicting [Set.fromList ps]))
        return $ toPathTrie $ nub paths

    shrink EmptyPathTrie = []
    shrink TerminalPathTrie = []
    shrink (PathTrie children) =
        IntMap.elems children
            ++ [ PathTrie (IntMap.fromDistinctAscList children')
               | children' <- subsequences (IntMap.toAscList children) \\ [IntMap.toAscList children]
               , not (null children')
               ]

-----------------------------------
------ Constructing test inputs
-----------------------------------

mkTestPaths1 :: [[Int]] -> [[Path]]
mkTestPaths1 = map (map (path . (: [])))

mkTestPathsN :: [[[Int]]] -> [[Path]]
mkTestPathsN = map (map path)

--------

spec :: Spec
spec = do
    describe "subpath checking" $ do
        it "empty path is strict subpath of nonempty" $
            property $
                \p -> p /= EmptyPath ==> isStrictSubpath EmptyPath p

        it "nothing is strict subpath of itself" $
            property $
                \p -> not $ isStrictSubpath p p

    describe "path tries" $ do
        it "fromPathTrie and toPathTrie are inverses" $ do
            property $ \pt -> toPathTrie (fromPathTrie pt) == pt

        it "PathTrie-based hasSubsumingMember same as set-based definition" $ do
            property $ \pt1 pt2 ->
                let pec1 = PathEClass (Set.fromList $ fromPathTrie pt1)
                    pec2 = PathEClass (Set.fromList $ fromPathTrie pt2)
                 in hasSubsumingMember pec1 pec2 == any (\p1 -> any (isStrictSubpath p1) (unPathEClass pec2)) (unPathEClass pec1)

    describe "PathEClass" $ do
        it "the trie and the set of a PathEClass hold the same paths" $ do
            property $ \pt ->
                let paths = fromPathTrie pt
                 in forAll (shuffle $ paths <> paths) $ \duplicated ->
                        let eclass = PathEClass $ Set.fromList duplicated
                         in fromPathTrie (getPathTrie eclass) == paths && Set.toAscList (unPathEClass eclass) == paths

    describe "mkEqConstraints" $ do
        it "removes unitary" $
            property $
                \ps -> mkEqConstraints (map (: []) ps) == EmptyConstraints

        it "removes empty" $
            property $
                \n -> mkEqConstraints (replicate n []) == EmptyConstraints

        it "completes equalities" $
            mkEqConstraints (mkTestPaths1 [[1, 2], [2, 3], [4, 5], [6, 7], [7, 1]])
                `shouldBe` EqConstraints (sort $ map (PathEClass . Set.fromList) $ mkTestPaths1 [[1, 2, 3, 6, 7], [4, 5]])

        it "adds congruences" $
            mkEqConstraints (mkTestPathsN [[[0], [1]], [[2], [0]], [[0, 0], [0, 1]]])
                `shouldBe` EqConstraints
                    ( sort
                        $ map (PathEClass . Set.fromList)
                        $ mkTestPathsN [[[0], [1], [2]], [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1]]]
                    )

        it "keeps the meaning of the classes it normalizes, and of a conjunction" $
            -- A term satisfies a class when every path of the class exists in
            -- it and the subterms there are equal.
            property $
                forAll ((,,) <$> classesGen <*> classesGen <*> termGen (3 :: Int)) $ \(left, right, term) -> do
                    satisfied (mkEqConstraints left) term `shouldBe` rawHolds left term
                    satisfied (combineEqConstraints (mkEqConstraints left) (mkEqConstraints right)) term
                        `shouldBe` rawHolds (left <> right) term

        it "detects contradictions from congruences" $
            -- This test input is from unifying `(a -> b) -> (a -> b)` and `(a -> (a -> a)) -> (a -> ([a] -> a))`
            constraintsAreContradictory
                ( mkEqConstraints $
                    mkTestPathsN
                        [ [[1, 1], [2, 1]]
                        , [[1, 1], [1, 2, 1], [1, 2, 2], [2, 1], [2, 2, 1, 0], [2, 2, 2]]
                        , [[1, 2], [2, 2]]
                        ]
                )
                `shouldBe` True

-- | Whether a term satisfies normalized equalities.
satisfied :: EqConstraints -> Tree.Tree Char -> Bool
satisfied constraints = equalitiesHold (equalityConstraint constraints)

{- | Whether a term satisfies raw classes: each path exists and the subterms
agree. A class of fewer than two distinct paths requires nothing, as
'mkEqConstraints' drops it.
-}
rawHolds :: [[Path]] -> Tree.Tree Char -> Bool
rawHolds classes term = all agree [paths | paths <- map nub classes, length paths > 1]
  where
    agree paths = case traverse (`getPath` term) paths of
        Just (first : rest) -> all (== first) rest
        Just [] -> True
        Nothing -> False

-- | One to three classes of two or three paths, each at most three long over child indices up to two.
classesGen :: Gen [[Path]]
classesGen = do
    count <- chooseInt (1, 3)
    vectorOf count $ do
        size <- chooseInt (2, 3)
        vectorOf size $ do
            len <- chooseInt (0, 3)
            path <$> vectorOf len (chooseInt (0, 2))

-- | A term over a, b, f of one child, and g of two, at most the given depth.
termGen :: Int -> Gen (Tree.Tree Char)
termGen 0 = elements [Tree.Node 'a' [], Tree.Node 'b' []]
termGen depth =
    oneof
        [ termGen 0
        , (\child -> Tree.Node 'f' [child]) <$> termGen (depth - 1)
        , (\left right -> Tree.Node 'g' [left, right]) <$> termGen (depth - 1) <*> termGen (depth - 1)
        ]
