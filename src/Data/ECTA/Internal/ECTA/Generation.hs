{- | Compiled generation for finite ECTAs.

The compiler turns every equality class into a shared value slot. Constraint
paths are local to the edge that owns them, so independently composed nested
constraints keep their ordinary ECTA meaning.
-}
module Data.ECTA.Internal.ECTA.Generation (
    GenerationPlan,
    GenerationPlanError (..),
    compileGenerationPlan,
    compileRootGenerationPlan,
    sampleGenerationPlan,
) where

import Control.Monad.State.Strict (StateT (..), evalStateT, get, put)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.Maybe (isNothing)
import qualified Data.Set as Set

import Data.ECTA.Internal.ECTA.Operations ()
import Data.ECTA.Internal.ECTA.Type
import Data.ECTA.Paths
import Data.ECTA.Term

-- | A checked finite generation plan.
data GenerationPlan = GenerationPlan !(IntMap.IntMap [SyncPlan]) !Plan

-- | Constructor choices and equality slots used by the sampler.
data Plan
    = Constant !Term
    | Construct !Symbol [Plan]
    | Choose !Int [Plan]
    | ChooseTerms !Int [Term]
    | Slot !Int Plan

-- | Equality values synchronized during one sample.
data SlotState = SlotState
    { slotValues :: !(IntMap.IntMap Term)
    , synchronizedSlots :: !IntSet.IntSet
    }

-- | The parts of one slot occurrence that contain nested slots.
data SyncPlan
    = SyncNone
    | SyncConstruct !Symbol [(Int, SyncPlan)]
    | SyncChoose [(Recognizer, SyncPlan)]
    | SyncSlot !Int

-- | A term-language check used at a synchronization choice.
data Recognizer
    = RecognizeTerm !Term
    | RecognizeConstruct !Symbol [Recognizer]
    | RecognizeChoice [Recognizer]
    | RecognizeTerms !(Set.Set Term)

-- | Failure to compile or sample a generation plan.
data GenerationPlanError
    = GenerationPlanRecursiveOrEmptyNode
    | GenerationPlanUnequalSlotLanguages [Path]
    | GenerationPlanInvalidChoiceIndex !Int !Int
    | GenerationPlanInconsistentSlots !Int
    deriving (Eq, Show)

{- | Compile a finite ECTA to a reusable generation plan.

Every equality class becomes one plan-local slot. The compiler checks that all
paths in a slot have the same reduced ECTA node. It supports constraints on any
edge and rejects recursive or empty nodes.
-}
compileGenerationPlan :: Node -> Either GenerationPlanError GenerationPlan
compileGenerationPlan root = do
    plan <- evalStateT (compileNode [] root) 0
    return $ GenerationPlan (collectOccurrences plan) plan
  where
    compileNode activeSlots node =
        wrapSlots activeSlots <$> compileNodeBody activeSlots node

    compileNodeBody activeSlots (Node edges) = do
        alternatives <- mapM (compileEdge activeSlots) edges
        case alternatives of
            [] -> liftError GenerationPlanRecursiveOrEmptyNode
            [alternative] -> return alternative
            _ -> return $ choosePlan alternatives
    compileNodeBody _ _ = liftError GenerationPlanRecursiveOrEmptyNode

    compileEdge activeSlots edge = do
        localSlots <- allocateSlots edge
        children <-
            mapM
                (uncurry compileNode)
                [ (descendSlots index (activeSlots <> localSlots), child)
                | (index, child) <- zip [0 ..] (edgeChildren edge)
                ]
        return $ wrapSlots localSlots (constructPlan (edgeSymbol edge) children)

    allocateSlots edge = do
        let eclasses = unsafeGetEclasses $ edgeEcs edge
        mapM_ (validateEclass edge) eclasses
        slotIds <- mapM (const freshSlot) eclasses
        return
            [ (slotPath, slotId)
            | (slotId, eclass) <- zip slotIds eclasses
            , slotPath <- unPathEClass eclass
            ]

    validateEclass edge eclass =
        case unPathEClass eclass of
            [] -> return ()
            firstPath : otherPaths ->
                let firstNode = nodeAt edge firstPath
                 in if all ((== firstNode) . nodeAt edge) otherPaths
                        then return ()
                        else liftError $ GenerationPlanUnequalSlotLanguages (unPathEClass eclass)

    nodeAt edge slotPath = getPath @Node @Node slotPath (Node [edge])

    descendSlots childIndex slots =
        [ (remainingPath, slotId)
        | (ConsPath index remainingPath, slotId) <- slots
        , index == childIndex
        ]

    wrapSlots slots plan =
        foldr Slot plan [slotId | (EmptyPath, slotId) <- slots]

    freshSlot = do
        slotId <- get
        put $ slotId + 1
        return slotId

    liftError = StateT . const . Left

-- | Retain the nested-slot routes for every equality slot occurrence.
collectOccurrences :: Plan -> IntMap.IntMap [SyncPlan]
collectOccurrences = go IntMap.empty
  where
    go occurrences (Constant _) = occurrences
    go occurrences (Construct _ children) = foldl go occurrences children
    go occurrences (Choose _ alternatives) = foldl go occurrences alternatives
    go occurrences (ChooseTerms _ _) = occurrences
    go occurrences (Slot slot body) =
        go withOccurrence body
      where
        withOccurrence = case compileSync body of
            Nothing -> occurrences
            Just sync -> IntMap.insertWith (<>) slot [sync] occurrences

-- | Retain only the routes that can bind nested equality slots.
compileSync :: Plan -> Maybe SyncPlan
compileSync (Constant _) = Nothing
compileSync (Construct symbol children) =
    case [(index, sync) | (index, Just sync) <- zip [0 ..] (map compileSync children)] of
        [] -> Nothing
        syncChildren -> Just $ SyncConstruct symbol syncChildren
compileSync (Choose _ alternatives)
    | all isNothing syncs = Nothing
    | otherwise =
        Just $
            SyncChoose
                [ (compileRecognizer alternative, maybe SyncNone id sync)
                | (alternative, sync) <- zip alternatives syncs
                ]
  where
    syncs = map compileSync alternatives
compileSync (ChooseTerms _ _) = Nothing
compileSync (Slot slot _) = Just $ SyncSlot slot

-- | Compile the language checks needed to select a synchronization branch.
compileRecognizer :: Plan -> Recognizer
compileRecognizer (Constant term) = RecognizeTerm term
compileRecognizer (Construct symbol children) =
    RecognizeConstruct symbol (map compileRecognizer children)
compileRecognizer (Choose _ alternatives) =
    RecognizeChoice $ map compileRecognizer alternatives
compileRecognizer (ChooseTerms _ terms) = RecognizeTerms $ Set.fromList terms
compileRecognizer (Slot _ body) = compileRecognizer body

{- | Compatibility name for 'compileGenerationPlan'.

The compiler no longer requires one root edge or root-only constraints.
-}
compileRootGenerationPlan :: Node -> Either GenerationPlanError GenerationPlan
compileRootGenerationPlan = compileGenerationPlan

-- | Fold a fully constant constructor into one shared term.
constructPlan :: Symbol -> [Plan] -> Plan
constructPlan symbol children =
    case traverse constantTerm children of
        Just terms -> Constant $ Term symbol terms
        Nothing -> Construct symbol children

-- | Fold a finite constant choice into shared term alternatives.
choosePlan :: [Plan] -> Plan
choosePlan alternatives =
    case traverse constantTerm alternatives of
        Just terms -> ChooseTerms (length terms) terms
        Nothing -> Choose (length alternatives) alternatives

-- | Extract the term from a constant plan.
constantTerm :: Plan -> Maybe Term
constantTerm (Constant term) = Just term
constantTerm _ = Nothing

{- | Sample a compiled plan.

The selector receives the number of alternatives and its state. The returned
term shares constant domain values and all repeated equality-slot values.
-}
sampleGenerationPlan ::
    (Int -> g -> (Int, g)) ->
    g ->
    GenerationPlan ->
    Either GenerationPlanError (Term, g)
sampleGenerationPlan select initialState plan =
    case plan of
        GenerationPlan occurrences root ->
            generate occurrences root initialState (SlotState IntMap.empty IntSet.empty) finish Left
  where
    finish term finalState _ = Right (term, finalState)

    generate _ (Constant term) current slots success _ = success term current slots
    generate occurrences (Construct symbol children) current slots success failure =
        generateChildren
            occurrences
            children
            current
            slots
            (\terms next slots' -> success (Term symbol terms) next slots')
            failure
    generate occurrences (Choose count alternatives) current slots success failure =
        let (index, next) = select count current
         in case atMay index alternatives of
                Just alternative -> generate occurrences alternative next slots success failure
                Nothing -> failure $ GenerationPlanInvalidChoiceIndex index count
    generate _ (ChooseTerms count terms) current slots success failure =
        let (index, next) = select count current
         in case atMay index terms of
                Just term -> success term next slots
                Nothing -> failure $ GenerationPlanInvalidChoiceIndex index count
    generate occurrences (Slot slot body) current slots success failure =
        case IntMap.lookup slot (slotValues slots) of
            Just term ->
                case bindSlot occurrences slot term slots of
                    nextSlots : _ -> success term current nextSlots
                    [] -> failure $ GenerationPlanInconsistentSlots slot
            Nothing ->
                generate
                    occurrences
                    body
                    current
                    slots
                    ( \term next slots' ->
                        case bindSlot occurrences slot term slots' of
                            nextSlots : _ -> success term next nextSlots
                            [] -> failure $ GenerationPlanInconsistentSlots slot
                    )
                    failure

    generateChildren _ [] current slots success _ = success [] current slots
    generateChildren occurrences (child : children) current slots success failure =
        generate
            occurrences
            child
            current
            slots
            ( \term next slots' ->
                generateChildren
                    occurrences
                    children
                    next
                    slots'
                    (\terms finalState slots'' -> success (term : terms) finalState slots'')
                    failure
            )
            failure

-- | Bind one slot and make every overlapping slot consistent with its term.
bindSlot ::
    IntMap.IntMap [SyncPlan] ->
    Int ->
    Term ->
    SlotState ->
    [SlotState]
bindSlot occurrences slot term slots = do
    consistent <- case IntMap.lookup slot (slotValues slots) of
        Nothing -> [slots{slotValues = IntMap.insert slot term (slotValues slots)}]
        Just existing
            | existing == term -> [slots]
            | otherwise -> []
    if IntSet.member slot (synchronizedSlots consistent)
        then return consistent
        else
            let synchronized =
                    consistent
                        { synchronizedSlots =
                            IntSet.insert slot (synchronizedSlots consistent)
                        }
             in foldl
                    (\states sync -> states >>= runSync occurrences sync term)
                    [synchronized]
                    (IntMap.findWithDefault [] slot occurrences)

-- | Bind the nested slots selected by one fixed outer term.
runSync ::
    IntMap.IntMap [SyncPlan] ->
    SyncPlan ->
    Term ->
    SlotState ->
    [SlotState]
runSync _ SyncNone _ slots = [slots]
runSync occurrences (SyncConstruct symbol children) (Term actual terms) slots
    | symbol == actual =
        foldl
            synchronizeChild
            [slots]
            children
    | otherwise = []
  where
    synchronizeChild states (index, child) = case atMay index terms of
        Nothing -> []
        Just term -> states >>= runSync occurrences child term
runSync occurrences (SyncChoose alternatives) term slots = do
    (recognizer, sync) <- alternatives
    if recognizes recognizer term
        then runSync occurrences sync term slots
        else []
runSync occurrences (SyncSlot slot) term slots =
    bindSlot occurrences slot term slots

-- | Check the branch of a term only when synchronization crosses a choice.
recognizes :: Recognizer -> Term -> Bool
recognizes (RecognizeTerm expected) actual = expected == actual
recognizes (RecognizeConstruct symbol children) (Term actual terms) =
    symbol == actual
        && length children == length terms
        && and (zipWith recognizes children terms)
recognizes (RecognizeChoice alternatives) term = any (`recognizes` term) alternatives
recognizes (RecognizeTerms terms) term = Set.member term terms

{-# INLINE sampleGenerationPlan #-}

-- | Index a list without throwing an exception.
atMay :: Int -> [a] -> Maybe a
atMay index _ | index < 0 = Nothing
atMay 0 (value : _) = Just value
atMay index (_ : values) = atMay (index - 1) values
atMay _ [] = Nothing
