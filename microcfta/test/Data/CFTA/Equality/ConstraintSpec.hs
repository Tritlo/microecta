module Data.CFTA.Equality.ConstraintSpec (spec) where

import qualified Data.IntMap.Lazy as IntMap
import Data.List (nub, sort, subsequences, (\\))
import qualified Data.Set as Set

import Test.Hspec
import Test.QuickCheck

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
