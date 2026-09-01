{-# LANGUAGE OverloadedStrings #-}

module Data.ECTA.IFCExpressionGenSpec (spec) where

import Data.List (isSuffixOf, sort)
import qualified Data.Map.Strict as Map
import Test.Hspec (Spec, describe, expectationFailure, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess)
import qualified Test.QuickCheck as QC

import Data.ECTA (
    Node (EmptyNode),
    Template (Hole, TemplateNode, TemplatePrefix),
    getAllTerms,
    matchesTemplate,
    termsMatching,
 )
import qualified Data.ECTA.Gen.QuickCheck as ECTAGen
import Data.ECTA.IFCExpressionLanguage
import Data.ECTA.Term (Symbol)

{- | Reference label semantics, independent of the generator: a value's label
is the join of every atom that can influence it, with a branch condition
influencing both branches.
-}
referenceLabel :: Expression -> Label
referenceLabel (IntLiteral _) = Public
referenceLabel (BoolLiteral _) = Public
referenceLabel (Variable name)
    | name == "secret" = Private
    | otherwise = Public
referenceLabel (Not value) = referenceLabel value
referenceLabel (ApplyBinary _ first second) =
    referenceLabel first `max` referenceLabel second
referenceLabel (IfExpression condition ifTrue ifFalse) =
    referenceLabel condition `max` referenceLabel ifTrue `max` referenceLabel ifFalse
referenceLabel (Print value) = referenceLabel value

-- | Infer a ground type independently of the generator.
referenceType :: Expression -> Maybe Type
referenceType (IntLiteral _) = Just TInt
referenceType (BoolLiteral _) = Just TBool
referenceType (Variable _) = Just TInt
referenceType (Not value) = do
    valueType <- referenceType value
    if valueType == TBool then Just TBool else Nothing
referenceType (ApplyBinary function_ first second) = do
    firstType <- referenceType first
    secondType <- referenceType second
    let homogeneous expected
            | firstType == expected && secondType == expected = Just expected
            | otherwise = Nothing
    case function_ of
        Equal
            | firstType == secondType, firstType /= TUnit -> Just TBool
            | otherwise -> Nothing
        Add -> homogeneous TInt
        Multiply -> homogeneous TInt
        Or -> homogeneous TBool
        And -> homogeneous TBool
referenceType (IfExpression condition ifTrue ifFalse) = do
    conditionType <- referenceType condition
    trueType <- referenceType ifTrue
    falseType <- referenceType ifFalse
    if conditionType == TBool && trueType == falseType && trueType /= TUnit
        then Just trueType
        else Nothing
referenceType (Print value) = do
    valueType <- referenceType value
    if valueType == TUnit then Nothing else Just TUnit

-- | A program leaks when a private value reaches its print.
leaks :: LabeledExpression -> Bool
leaks program = referenceLabel (expression program) == Private

-- | The generated annotations must agree with the reference semantics.
faithfullyLabeled :: LabeledExpression -> Bool
faithfullyLabeled value =
    referenceType (expression value) == Just (expressionType value)
        && referenceLabel (expression value) == expressionLabel value

-- | The smallest leaking program.
minimalLeak :: LabeledExpression
minimalLeak = LabeledExpression TUnit Private (Print (Variable "secret"))

{- | The fields 'Eq' compares, which the custom 'Show' hides. Comparing these
makes a failure name the differing field.
-}
keyAndExpression :: LabeledExpression -> (Labeled, Expression)
keyAndExpression value = (securityKey value, expression value)

spec :: Spec
spec =
    describe "information-flow expression generation" $ do
        it "counts the depth-at-most-one labeled language exactly" $ do
            ECTAGen.cardinality (ECTAGen.ungroup (expressionsUpToDepth 1))
                `shouldBe` Right 108
            ECTAGen.sizes (expressionsUpToDepth 1)
                `shouldBe` Right
                    ( Map.fromList
                        [ ((TInt, Public), 39)
                        , ((TInt, Private), 29)
                        , ((TBool, Public), 33)
                        , ((TBool, Private), 7)
                        ]
                    )

        it "annotates every program with the reference type and label" $
            case ECTAGen.pmf (ECTAGen.ungroup (programsUpToDepth 1)) of
                Left err -> expectationFailure $ show err
                Right outcomes ->
                    all (faithfullyLabeled . fst) outcomes `shouldBe` True

        it "counts the leaking programs without enumerating them" $
            ECTAGen.sizes (programsUpToDepth 1)
                `shouldBe` Right
                    ( Map.fromList
                        [ ((TUnit, Public), 72)
                        , ((TUnit, Private), 36)
                        ]
                    )

        it "finds the smallest leaking program as a query" $
            fmap
                (fmap keyAndExpression)
                (ECTAGen.smallest (ECTAGen.atKey (TUnit, Private) (programsUpToDepth 1)))
                `shouldBe` Right (Just (keyAndExpression minimalLeak))

        it "cannot represent a leak under the enforcing print" $ do
            ECTAGen.smallest (ECTAGen.atKey (TUnit, Private) (secureProgramsUpToDepth 1))
                `shouldBe` Right Nothing
            -- Not vacuous: the enforcing print does admit the public programs.
            ECTAGen.sizes (secureProgramsUpToDepth 1)
                `shouldBe` Right (Map.fromList [((TUnit, Public), 72)])

        it "shrinks a QuickCheck leak to the minimal program" $ do
            let generator = ECTAGen.ungroup (programsUpToDepth 2)
            result <-
                QC.quickCheckWithResult QC.stdArgs{QC.chatty = False, QC.maxSuccess = 500} $
                    ECTAGen.forAll generator $
                        \program -> not (leaks program)
            case result of
                QC.Failure{QC.failingTestCase = [shown]} ->
                    shown `shouldSatisfy` (show minimalLeak `isSuffixOf`)
                _ -> expectationFailure "expected the no-leak property to fail"

        modifyMaxSuccess (const 500) $
            it "samples only leak-free programs from the enforcing print" $
                QC.forAll (ECTAGen.toGen (ECTAGen.ungroup (secureProgramsUpToDepth 2))) $
                    \program ->
                        QC.counterexample (show program <> " :: " <> show (securityKey program)) $
                            QC.property $
                                faithfullyLabeled program && not (leaks program)

        it "agrees with the count oracle on exact counts" $ do
            programCountUpToDepth 1 `shouldBe` 108
            map (expressionCountUpTo 1) expressionKeys `shouldBe` [39, 29, 33, 7]
            ECTAGen.cardinality (ECTAGen.ungroup (programsUpToDepth 2))
                `shouldBe` Right (programCountUpToDepth 2)

        modifyMaxSuccess (const 500) $
            it "samples faithfully labeled programs from the handwritten baseline" $
                QC.forAll (handwrittenProgramGen 2) $ \program ->
                    QC.counterexample (show program <> " :: " <> show (securityKey program)) $
                        QC.property $
                            faithfullyLabeled program

        -- The practical generator computes its label with practicalLabel, a copy
        -- of referenceLabel, so only the type half says anything here.
        modifyMaxSuccess (const 500) $
            it "samples programs of the reference type from the practical baseline" $
                QC.forAll (practicalProgramGen 2) $ \program ->
                    QC.counterexample (show program <> " :: " <> show (securityKey program)) $
                        QC.property $
                            referenceType (expression program) == Just (expressionType program)

        it "builds the surface automaton with the exact counts" $ do
            length (getAllTerms (surfaceProgramNode 1 Public)) `shouldBe` 72
            length (getAllTerms (surfaceProgramNode 1 Private)) `shouldBe` 36
            map termToExpression (getAllTerms (surfaceProgramNode 1 Private))
                `shouldSatisfy` all (maybe False ((== Private) . referenceLabel))

        it "answers the secret-branching shape as a template restriction" $ do
            termsMatching branchesOnSecret (surfaceProgramNode 2 Public)
                `shouldBe` EmptyNode
            let restricted =
                    getAllTerms $
                        termsMatching branchesOnSecret (surfaceProgramNode 2 Private)
                byFilter =
                    filter (matchesTemplate branchesOnSecret) $
                        getAllTerms (surfaceProgramNode 2 Private)
            length restricted `shouldBe` 24896
            sort byFilter `shouldBe` sort restricted
            map termToExpression restricted
                `shouldSatisfy` all (maybe False ((== Private) . referenceLabel))

        it "reads the restricted automaton back as a generator" $ do
            -- The largest member is print of an if whose guard holds three
            -- nodes and whose branches hold four each: 13 nodes.
            let branchy =
                    ECTAGen.upToSize 13 $
                        ECTAGen.fromECTA $
                            termsMatching branchesOnSecret (surfaceProgramNode 2 Private)
            ECTAGen.cardinality branchy `shouldBe` Right 24896

{- | Programs whose conditional guard is an equality test whose first operand
is the secret. That is narrower than "consults the secret in a guard": the
template pins the guard's top node.
-}
branchesOnSecret :: Template Symbol
branchesOnSecret =
    TemplateNode
        "print"
        [TemplatePrefix "if" [TemplatePrefix "==" [TemplateNode "secret" []], Hole, Hole]]
