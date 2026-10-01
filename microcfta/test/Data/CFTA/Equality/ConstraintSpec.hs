module Data.CFTA.Equality.ConstraintSpec (spec) where

import qualified Data.IntMap.Lazy as IntMap
import Data.List (nub, sort, subsequences, (\\))
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
        paths <- suchThat arbitrary (\ps -> not (isContradicting [ps]))
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
        it "empty path is always subpath" $
            property $
                \p -> isSubpath EmptyPath p

        it "is subpath of concatenation" $
            property $
                \xs ys -> isSubpath (path xs) (path $ xs ++ ys)

        it "non-empty concatenation is not subpath of orig" $
            property $
                \xs ys -> ys /= [] ==> not $ isSubpath (path $ xs ++ ys) (path xs)

        it "empty path is strict subpath of nonempty" $
            property $
                \p -> p /= EmptyPath ==> isStrictSubpath EmptyPath p

        it "nothing is strict subpath of itself" $
            property $
                \p -> not $ isStrictSubpath p p

    describe "substSubpath" $ do
        it "replaces prefix" $
            property $
                \xs ys zs -> substSubpath (path zs) (path ys) (path $ ys ++ xs) `shouldBe` path (zs ++ xs)

    describe "path tries" $ do
        it "fromPathTrie and toPathTrie are inverses" $ do
            property $ \pt -> toPathTrie (fromPathTrie pt) == pt

        it "PathTrie-based hasSubsumingMember same as list-based implementation" $ do
            property $ \pt1 pt2 ->
                let pec1 = PathEClass (fromPathTrie pt1)
                    pec2 = PathEClass (fromPathTrie pt2)
                 in hasSubsumingMember pec1 pec2 == hasSubsumingMemberListBased (unPathEClass pec1) (unPathEClass pec2)

    describe "PathEClass" $ do
        it "both ways of getting list of paths from a PathEClass are identical" $ do
            property $ \pt ->
                let paths = fromPathTrie pt
                 in forAll (shuffle $ paths <> paths) $ \duplicated ->
                        let eclass = PathEClass duplicated
                         in fromPathTrie (getPathTrie eclass) == paths && getOrigPaths eclass == paths

    describe "mkEqConstraints" $ do
        it "removes unitary" $
            property $
                \ps -> mkEqConstraints (map (: []) ps) == EmptyConstraints

        it "removes empty" $
            property $
                \n -> mkEqConstraints (replicate n []) == EmptyConstraints

        it "completes equalities" $
            mkEqConstraints (mkTestPaths1 [[1, 2], [2, 3], [4, 5], [6, 7], [7, 1]])
                `shouldBe` rawMkEqConstraints (sort $ mkTestPaths1 [[1, 2, 3, 6, 7], [4, 5]])

        it "adds congruences" $
            mkEqConstraints (mkTestPathsN [[[0], [1]], [[2], [0]], [[0, 0], [0, 1]]])
                `shouldBe` rawMkEqConstraints (sort (mkTestPathsN [[[0], [1], [2]], [[0, 0], [0, 1], [1, 0], [1, 1], [2, 0], [2, 1]]]))

        it "keeps the meaning of the classes it normalizes, and of a conjunction" $
            -- A term satisfies a class when every path of the class exists in
            -- it and the subterms there are equal.
            property $
                forAll ((,,) <$> classesGen <*> classesGen <*> termGen (3 :: Int)) $ \(left, right, term) -> do
                    satisfied (mkEqConstraints left) term `shouldBe` rawHolds left term
                    satisfied (combineEqConstraints (mkEqConstraints left) (mkEqConstraints right)) term
                        `shouldBe` rawHolds (left <> right) term
                    -- An implication is sound: a term that satisfies the left satisfies the right.
                    (constraintsImply (mkEqConstraints left) (mkEqConstraints right) && rawHolds left term && not (rawHolds right term))
                        `shouldBe` False
                    -- Classes imply the normalized form of any one of them.
                    constraintsImply (mkEqConstraints left) (mkEqConstraints (take 1 left)) `shouldBe` True

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

    constraintsImplySpec

-- Skipped, not deleted: QuickCheck generates path lists far larger than any
-- real input, and 'mkEqConstraints' saturates congruences quadratically in
-- them, so these take too long to keep in the suite. Open since 2021-06-23.
-- 'constraintsImply' is covered by the examples above instead.
constraintsImplySpec :: Spec
constraintsImplySpec = describe "constraintsImply" $ do
    xit "implies removed constraints" $
        property $ \cs1 cs2 ->
            length (concat cs1) < 300
                && length (concat cs2)
                    < 300
                ==> constraintsImply (mkEqConstraints $ cs1 ++ cs2) (mkEqConstraints cs1)

    xit "does not imply added constraints" $
        property $ \cs1 cs2 ->
            length (concat cs1) < 300
                && length (concat cs2)
                    < 300
                ==> let ecs1 = mkEqConstraints $ cs1 ++ cs2
                        ecs2 = mkEqConstraints cs1
                     in ecs1 /= ecs2 ==> not (constraintsImply ecs2 ecs1)

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
