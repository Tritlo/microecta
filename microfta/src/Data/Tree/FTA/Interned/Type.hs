-- | Interned nodes and edges with a constraint parameter.
module Data.Tree.FTA.Interned.Type (
    RecNodeId (..),
    Edge (.., Edge),
    UninternedEdge (..),
    mkEdge,
    mkNode,
    emptyEdge,
    edgeChildren,
    edgeConstraint,
    edgeSymbol,
    setChildren,
    Node (.., Node, Mu),
    InternedNode (..),
    InternedMu (..),
    UninternedNode (..),
    IntersectId,
    pattern IntersectId,
    nodeIdentity,
    numNestedMu,
    substFree,
    freeVars,
    modifyNode,
    createMu,
    createMuDontCleanup,
    shape,
    matchMu,
) where

import Data.CacheFamily (CacheFamily, newCacheFamily, selectCache)
import Data.Function (on)
import Data.Hashable (Hashable (..))
import Data.IORef (IORef, newIORef)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Type.Reflection (Typeable)

import System.IO.Unsafe (unsafePerformIO)

import Data.Interned.Extended.HashTableBased

import Data.Memoization
import Data.Tree.FTA.Constraint (Constraint (..))

-- Mu node table

-- | Internal identifier for references to recursive Interned automaton nodes.
data RecNodeId
    = -- | Reference to the 'Id' of an interned 'Mu' node
      RecInt !Id
    | {- | Reference to an as-yet uninterned 'Mu' node, for which the 'Id' is not yet known

      The 'Int' argument is used to distinguish between multiple nested 'Mu' nodes.

      NOTE: This is intentionally not an 'Id': it does not refer to the 'Id' of any interned node.
      -}
      RecUnint Int
    | {- | Placeholder variable that we use /only/ for depth calculations

      The invariant that this is used /only/ for depth calculations, along with the observation that depth calculation
      does not depend on the exact choice of variable, justifies subtituting any other variable for 'RecDepth' in terms
      containing 'RecDepth' in all contexts.
      -}
      RecDepth
    | {- | Refer to a 'Mu' node that @intersect@ is about to construct

      Having a constructor here for one algorithm is not elegant. Parameterizing
      @Node@ over the type of identifier it carries would be better, and would
      also rule out most of the other cases: outside these algorithms every node
      is fully interned and 'RecInt' is the only constructor that can appear.
      That change has not been made.
      -}
      RecIntersect IntersectId
    deriving (Eq, Ord, Show)

{- | Pair of node identities naming the recursive node introduced by @intersect@.

This is a context-free way to name a 'Mu' node before its 'Id' exists. It
generalizes "refer to the immediately enclosing binder": all we need is /some/
concrete way to name that node without an 'Id'. Intersection introduces a 'Mu'
whenever it meets a 'Mu' on either side, and does not introduce a second one
for the same intersection problem in the same scope, so the 'Id's of the two
operands identify the node to be constructed uniquely. Seeing a call to
intersect again with those same two operands - whatever kind of nodes they are
- can therefore refer back to it.

Intersection introduces a 'Mu' in three cases ('Mu' on both sides, on the left
only, or on the right only), but the distinction does not matter here: the two
operand 'Id's are the whole name.

Because free variables are cached in a term, checking whether the 'Mu' node is
needed at all is cheap. So if the input graphs never refer past a 'Mu', the
output does not either: no redundant 'Mu' nodes are introduced.
-}
data IntersectId
    = -- Invariant: the two 'Id's should be ordered (guaranteed by the pattern synonym constructor)
      UnsafeIntersectId !Id !Id
    deriving (Eq, Ord, Show)

-- | Smart pattern that stores the two ids in canonical order.
pattern IntersectId :: Id -> Id -> IntersectId
pattern IntersectId i j <- (UnsafeIntersectId i j)
  where
    IntersectId i j
        | i <= j = UnsafeIntersectId i j
        | otherwise = UnsafeIntersectId j i

instance Hashable RecNodeId where
    hashWithSalt salt (RecInt nodeId) =
        salt `hashWithSalt` (0 :: Int) `hashWithSalt` nodeId
    hashWithSalt salt (RecUnint nodeId) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` nodeId
    hashWithSalt salt RecDepth =
        salt `hashWithSalt` (2 :: Int)
    hashWithSalt salt (RecIntersect intersectionId) =
        salt `hashWithSalt` (3 :: Int) `hashWithSalt` intersectionId

instance Hashable IntersectId where
    hashWithSalt salt (UnsafeIntersectId left right) =
        salt `hashWithSalt` left `hashWithSalt` right

-- Edges

-- | One outgoing alternative of an Interned automaton node.
data Edge symbol constraint = InternedEdge
    { edgeId :: !Id
    , uninternedEdge :: !(UninternedEdge symbol constraint)
    }

instance (Show symbol, Show constraint, Constraint constraint) => Show (Edge symbol constraint) where
    show e
        | edgeConstraint e == noConstraint = "(Edge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ ")"
        | otherwise = "(mkEdge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeConstraint e) ++ ")"

-- | Symbol at the root of terms accepted through this edge.
{-# INLINEABLE edgeSymbol #-}
edgeSymbol :: Edge symbol constraint -> symbol
edgeSymbol = uEdgeSymbol . uninternedEdge

-- | Child automata for this edge.
{-# INLINEABLE edgeChildren #-}
edgeChildren :: Edge symbol constraint -> [Node symbol constraint]
edgeChildren = uEdgeChildren . uninternedEdge

-- | The constraint attached to this transition.
{-# INLINEABLE edgeConstraint #-}
edgeConstraint :: Edge symbol constraint -> constraint
edgeConstraint = uEdgeConstraint . uninternedEdge

instance Eq (Edge symbol constraint) where
    (InternedEdge{edgeId = n1}) == (InternedEdge{edgeId = n2}) = n1 == n2

instance Ord (Edge symbol constraint) where
    compare = compare `on` edgeId

instance Hashable (Edge symbol constraint) where
    hashWithSalt s e = s `hashWithSalt` (edgeId e)

-- Nodes

-- | Interned recursive node payload.
data InternedMu symbol constraint = MkInternedMu
    { internedMuId :: {-# UNPACK #-} !Id
    -- ^ 'Id' of the node itself
    , internedMuBody :: !(Node symbol constraint)
    {- ^ The body of the 'Mu'

    Recursive occurrences of this node are

    > Rec (RecInt internedMuId)
    -}
    , internedMuShape :: !(Node symbol constraint)
    {- ^ The body of the 'Mu', before it was assigned an 'Id'

    Invariant:

    >    substFree (RecInt internedMuId) (Rec (RecUnint (numNestedMu internedMuBody))) internedMuBody
    > == internedMuShape
    -}
    , internedMuDepthShape :: !(Node symbol constraint)
    {- ^ The body applied to 'RecDepth'.

    This distinguishes a binder that uses its argument from a nested,
    redundant binder whose captured outer reference happens to equal the
    ordinary shape placeholder.
    -}
    }

-- | Interned non-recursive node payload.
data InternedNode symbol constraint = MkInternedNode
    { internedNodeId :: {-# UNPACK #-} !Id
    -- ^ The 'Id' of the node itself
    , internedNodeEdges :: ![Edge symbol constraint]
    -- ^ All outgoing edges
    , internedNodeNumNestedMu :: !Int
    -- ^ Maximum Mu nesting depth in the term
    , internedNodeFree :: !(Set RecNodeId)
    -- ^ Free variables in the term
    }

-- | Interned automaton node.
data Node symbol constraint
    = -- | Interned node with one or more outgoing alternatives.
      InternedNode {-# UNPACK #-} !(InternedNode symbol constraint)
    | -- | Empty language.
      EmptyNode
    | -- | Interned recursive node.
      InternedMu {-# UNPACK #-} !(InternedMu symbol constraint)
    | -- | Recursive reference used inside a 'Mu'.
      Rec !RecNodeId

instance Eq (Node symbol constraint) where
    InternedNode l == InternedNode r = internedNodeId l == internedNodeId r
    InternedMu l == InternedMu r = internedMuId l == internedMuId r
    Rec l == Rec r = l == r
    EmptyNode == EmptyNode = True
    _ == _ = False

instance (Show symbol, Show constraint, Constraint constraint) => Show (Node symbol constraint) where
    show (InternedNode node) = "(Node " <> show (internedNodeEdges node) <> ")"
    show EmptyNode = "EmptyNode"
    show (InternedMu mu) = "(Mu " <> show (internedMuId mu) <> " " <> show (internedMuBody mu) <> ")"
    show (Rec n) = "(Rec " <> show n <> ")"

instance Ord (Node symbol constraint) where
    compare n1 n2 = compare (nodeDescriptorInt n1) (nodeDescriptorInt n2)
      where
        nodeDescriptorInt :: Node symbol constraint -> Int
        nodeDescriptorInt EmptyNode = -1
        nodeDescriptorInt (InternedNode node) = 3 * i
          where
            i = internedNodeId node
        nodeDescriptorInt (InternedMu mu) = 3 * i + 1
          where
            i = internedMuId mu
        nodeDescriptorInt (Rec recId) = 3 * i + 2
          where
            i = case recId of
                RecInt nid -> nid
                _otherwise -> error $ "compare: unexpected " <> show recId

instance Hashable (Node symbol constraint) where
    hashWithSalt s EmptyNode = s `hashWithSalt` (-1 :: Int)
    hashWithSalt s (InternedMu mu) = s `hashWithSalt` (-2 :: Int) `hashWithSalt` i
      where
        i = internedMuId mu
    hashWithSalt s (Rec i) = s `hashWithSalt` (-3 :: Int) `hashWithSalt` i
    hashWithSalt s (InternedNode node) = s `hashWithSalt` i
      where
        i = internedNodeId node

{- | Maximum number of nested Mus in the term

@O(1)@ provided that there are no unbounded Mu chains in the term.
-}
{-# INLINEABLE numNestedMu #-}
numNestedMu :: Node symbol constraint -> Int
numNestedMu EmptyNode = 0
numNestedMu (InternedNode node) = internedNodeNumNestedMu node
numNestedMu (InternedMu mu) = 1 + numNestedMu (internedMuBody mu)
numNestedMu (Rec _) = 0

{- | Free variables in the term

@O(1)@ in the size of the graph, provided that there are no unbounded Mu chains in the term.
@O(log n)@ in the number of free variables in the graph, which we expect to be orders of magnitude smaller than the
size of the graph (indeed, we don't expect more than a handful).
-}
{-# INLINEABLE freeVars #-}
freeVars :: Node symbol constraint -> Set RecNodeId
freeVars EmptyNode = Set.empty
freeVars (InternedNode node) = internedNodeFree node
freeVars (InternedMu mu) = Set.delete (RecInt (internedMuId mu)) (freeVars (internedMuBody mu))
freeVars (Rec i) = Set.singleton i

-- Getters and setters

-- | Stable interned identity for non-empty, interned nodes.
{-# INLINEABLE nodeIdentity #-}
nodeIdentity :: Node symbol constraint -> Id
nodeIdentity (InternedMu mu) = internedMuId mu
nodeIdentity (InternedNode node) = internedNodeId node
nodeIdentity (Rec (RecInt i)) = i
nodeIdentity _ = error "nodeIdentity: unexpected empty or unresolved node"

-- | Replace an edge's children while preserving its symbol and constraints.
{-# INLINEABLE setChildren #-}
setChildren ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> [Node symbol constraint] -> Edge symbol constraint
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeConstraint e)

-- Interning Nodes

-- | Non-canonical node description used before hash-consing.
data UninternedNode symbol constraint
    = UninternedNode ![Edge symbol constraint]
    | UninternedEmptyNode
    | {- | Recursive node, carrying its shape alongside the function.

      The function should be parametric in the Id:

      > substFree i (Rec j) (f i) == f j

      The shape is the result of applying 'shape' to the function, stored
      rather than recomputed. Computing it
      builds nodes, which interns them, so leaving it to 'Eq' or 'Hashable'
      would make hashing an uninterned node re-enter the interning cache. The
      strict field forces it while the value is still being constructed, which
      is before 'intern' looks at anything. See 'shape'.

      The first node is the body applied to 'RecDepth'; the second is its
      ordinary 'shape'. Keeping both distinguishes a real recursive binder
      from a redundant nested one whose captured outer reference happens to
      equal the ordinary shape placeholder. Without that distinction, the
      unused binder can reuse the recursive node before 'createMu' removes it.
      -}
      UninternedMu
        !(Node symbol constraint)
        !(Node symbol constraint)
        !(RecNodeId -> Node symbol constraint)

instance Eq (UninternedNode symbol constraint) where
    UninternedNode es == UninternedNode es' = es == es'
    UninternedEmptyNode == UninternedEmptyNode = True
    UninternedMu depthShape s _ == UninternedMu depthShape' s' _ = depthShape == depthShape' && s == s'
    _ == _ = False

instance Hashable (UninternedNode symbol constraint) where
    hashWithSalt salt = go
      where
        go :: UninternedNode symbol constraint -> Int
        go UninternedEmptyNode = salt `hashWithSalt` (0 :: Int)
        go (UninternedNode es) = salt `hashWithSalt` (1 :: Int) `hashWithSalt` es
        go (UninternedMu depthShape s _) =
            salt
                `hashWithSalt` (2 :: Int)
                `hashWithSalt` depthShape
                `hashWithSalt` s

-- | Typed node caches share one identity sequence across all automaton types.
nodeCaches :: CacheFamily
nodeCaches = unsafePerformIO newCacheFamily
{-# NOINLINE nodeCaches #-}

-- | Next identity for a node in any typed cache.
nodeIds :: IORef Id
nodeIds = unsafePerformIO (newIORef 0)
{-# NOINLINE nodeIds #-}

-- | Return the canonical node in its typed cache.
{-# INLINEABLE internNode #-}
internNode ::
    forall symbol constraint.
    (Typeable symbol, Typeable constraint) => UninternedNode symbol constraint -> Node symbol constraint
internNode = intern (selectCache nodeCaches (freshCacheWith nodeIds)) identifyNode

{-# INLINEABLE identifyNode #-}
identifyNode :: Id -> UninternedNode symbol constraint -> Node symbol constraint
identifyNode i (UninternedNode es) =
    InternedNode $
        MkInternedNode
            { internedNodeId = i
            , internedNodeEdges = es
            , internedNodeNumNestedMu = maximum (0 : [numNestedMu child | edge <- es, child <- edgeChildren edge])
            , internedNodeFree = Set.unions [freeVars child | edge <- es, child <- edgeChildren edge]
            }
identifyNode _ UninternedEmptyNode = EmptyNode
identifyNode i (UninternedMu depthShape s n) =
    InternedMu $
        MkInternedMu
            { internedMuId = i
            , internedMuBody = n (RecInt i)
            , -- In order to establish the invariant for internedMuNoId, we need to know
              --
              -- >    substFree (RecInt internedMuId) (Rec (RecUnint (numNestedMu internedMuBody))) internedMuBody
              -- > == internedMuShape
              --
              -- This follows from parametricity:
              --
              -- >    internedMuShape
              -- >      -- { definition of internedMuShape }
              -- > == shape n
              -- >      -- { definition of shape }
              -- > == n (RecUnint (numNestedMu (n RecDepth)))
              -- >      -- { by parametricity, depth is independent of the variable number }
              -- > == n (RecUnint (numNestedMu (n (RecInt i))))
              -- >      -- { parametricity again }
              -- > == substFree (RecInt i) (Rec (RecUnint (numNestedMu (n (RecInt i))))) (n (RecInt i))
              -- >      -- { definition of internedMuId and internedMuBody }
              -- > == substFree (RecInt internedMuId) (Rec (RecUnint (numNestedMu internedMuBody))) internedMuBody
              --
              -- QED.
              internedMuShape = s
            , internedMuDepthShape = depthShape
            }

{- | Compute the " shape " of the body of a 'Mu'

During interning we need to know the shape of the body of a 'Mu' node /before/ we know the 'Id' of that node. We do
this by replacing any 'Rec' nodes in the node by placeholders. We have to be careful here however to correctly assign
placeholders in the presence of nested 'Mu' nodes. For example, if the user writes a term such as

> -- f (f (f ... (g (g (g ... a)))))
> Mu $ \r -> Node [
>     Edge "f" [r]
>   , Edge "g" [ Mu $ \r' -> Node [
>                    Edge "g" [r']
>                  , Edge "a" []
>                  ]
>              ]
>   ]

we should be careful not to accidentially identify @r@ and @r'@.

Precondition: the function must be parametric in the choice of variable names:

> substFree i (Rec j) (f i) == f j

Put another way, we must rule out /exotic terms/: in our case, exotic terms would be uninterned @Mu@ nodes that
have one shape when given one variable, and another shape when given a different variable. We do not have such terms.
(Of course, a function such as substitution /does/ do one thing if it sees one variable and another thing when it
sees a different variable, but this is okay: substitution is a function /on/ terms, mapping non-exotic terms to
non-exotic terms.)

Implementation note: We are calling the function twice: once to compute the depth of the node, and then a second time
to give it the right placeholder variable. Some observations:

o Semantically, this is okay; if we were working with a first order representation, it would be the equivalent of
  first executing some kind of function @Node -> Int@, followed by some kind of substitution @Node -> Node@. It's the
  same with the higher order representation, except that in /principle/ the function could do entirely different
  things when given 'RecDepth' versus some other kind of placeholder; the parametricity precondition rules this out.
o It's slightly inefficient, but since this lives at the user interface boundary only, performance here is not
  critical: internally we work with interned nodes only, and this function is not relevant.
o It /is/ important that the placeholder we pick here is uniquely determined by the node itself: this is what
  justifies using 'shape' during interning.
-}
{-# INLINEABLE shape #-}
shape :: (RecNodeId -> Node symbol constraint) -> Node symbol constraint
shape f = f (RecUnint (numNestedMu (f RecDepth)))

-- Interning Edges

-- | Edge payload before interning.
data UninternedEdge symbol constraint = UninternedEdge
    { uEdgeSymbol :: !symbol
    , uEdgeChildren :: ![Node symbol constraint]
    , uEdgeConstraint :: !constraint
    }
    deriving (Eq)

instance (Hashable symbol, Constraint constraint) => Hashable (UninternedEdge symbol constraint) where
    hashWithSalt salt (UninternedEdge symbol children ecs) =
        salt `hashWithSalt` symbol `hashWithSalt` children `hashWithSalt` ecs

-- | Typed edge caches share one identity sequence across all automaton types.
edgeCaches :: CacheFamily
edgeCaches = unsafePerformIO newCacheFamily
{-# NOINLINE edgeCaches #-}

-- | Next identity for an edge in any typed cache.
edgeIds :: IORef Id
edgeIds = unsafePerformIO (newIORef 0)
{-# NOINLINE edgeIds #-}

-- | Return the canonical edge in its typed cache.
{-# INLINEABLE internEdge #-}
internEdge ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) => UninternedEdge symbol constraint -> Edge symbol constraint
internEdge = intern (selectCache edgeCaches (freshCacheWith edgeIds)) InternedEdge

-- Smart constructors

-- Edge constructors

-- | Build or match an unconstrained edge.
pattern Edge ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol -> [Node symbol constraint] -> Edge symbol constraint
pattern Edge s ns <- (InternedEdge _ (UninternedEdge s ns _))
  where
    Edge s ns = internEdge $ UninternedEdge s ns noConstraint

{-# COMPLETE Edge #-}

-- | Edge that is guaranteed to be removed when a node is built.
{-# INLINEABLE emptyEdge #-}
emptyEdge :: (Hashable symbol, Typeable symbol, Constraint constraint) => symbol -> Edge symbol constraint
emptyEdge symbol = Edge symbol [EmptyNode]

{-# INLINEABLE isEmptyEdge #-}
isEmptyEdge :: Edge symbol constraint -> Bool
isEmptyEdge = elem EmptyNode . edgeChildren

{-# INLINEABLE removeEmptyEdges #-}
removeEmptyEdges :: [Edge symbol constraint] -> [Edge symbol constraint]
removeEmptyEdges = filter (not . isEmptyEdge)

-- | Build an edge with transition constraints.
{-# INLINEABLE mkEdge #-}
mkEdge ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    symbol -> [Node symbol constraint] -> constraint -> Edge symbol constraint
mkEdge s ns ecs
    | contradictory ecs = emptyEdge s
    | otherwise = internEdge $ UninternedEdge s ns ecs

-- Node constructors

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}

-- | Build or match a non-empty node from outgoing alternatives.
pattern Node :: (Typeable symbol, Typeable constraint) => [Edge symbol constraint] -> Node symbol constraint
pattern Node es <- (InternedNode (internedNodeEdges -> es))
  where
    Node = mkNode

-- | Intern a set of alternatives and discard edges with empty children.
{-# INLINEABLE mkNode #-}
mkNode :: (Typeable symbol, Typeable constraint) => [Edge symbol constraint] -> Node symbol constraint
mkNode es = case removeEmptyEdges es of
    [] -> EmptyNode
    es' -> internNode $ UninternedNode $ Set.toList $ Set.fromList es'

{- | An optimized Node constructor that avoids the interning/preprocessing of the Node constructor
  when nothing changes
-}
{-# INLINEABLE modifyNode #-}
modifyNode ::
    (Typeable symbol, Typeable constraint) =>
    Node symbol constraint -> ([Edge symbol constraint] -> [Edge symbol constraint]) -> Node symbol constraint
modifyNode n@(Node es) f =
    let es' = f es
     in if es' == es
            then
                n
            else
                Node es'
modifyNode _ _ = error "modifyNode: unexpected empty, recursive, or unresolved node"

-- Mu

{- | Pattern only a Mu constructor

When we go underneath a Mu constructor, we need to bind the corresponding Rec node to something: that's why pattern
matching on 'Mu' yields a function. Code that wants to traverse the term as-is should match on the interned
constructors instead (and then deal with the dangling references).

An identity function

> foo (Mu f) = Mu f

will run in O(1) time:

> foo (Mu f) = Mu f
>   -- { expand view patern }
> foo node | Just f <- matchMu node = createMu f
>   -- { case for @InternedMu mu@ }
> foo (InternedMu mu) | Just f <- matchMu (InternedMu m) = createMu f
>   -- { definition of matchMu }
> foo (InternedMu mu) = let f = \n' ->
>                          if | n' == Rec (RecUnint (numNestedMu (internedMuBody mu))) ->
>                                internedMuShape mu
>                            | n' == Rec RecDepth ->
>                                internedMuShape mu
>                            | otherwise ->
>                                substFree (internedMuId mu) n' (internedMuBody mu)
>                       in createMu f
>   -- { definition of createMu }
> foo (InternedMu mu) =
>   let g = f . Rec
>       bodyAtDepth = g RecDepth
>   in internNode $ UninternedMu bodyAtDepth (g (RecUnint (numNestedMu bodyAtDepth))) g

Before calling `intern`, `createMu` computes and stores both the body at
`RecDepth` and its ordinary shape in the `UninternedMu`. The stored depth probe
is reused to choose the shape placeholder, so the body function is evaluated
twice in total. 'matchMu' reuses both forms, so rebuilding an unchanged 'Mu'
stays @O(1)@. Equality, hashing, and identification do not invoke the function
inside the interning cache.
-}
pattern Mu ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint
pattern Mu f <- (matchMu -> Just f)
  where
    Mu = createMu

{- | Construct recursive node

A 'Mu' whose variable does not occur in its body binds nothing, so the body is returned on its own. Intersection
already avoids introducing such nodes (see @maybeMu@); doing it here covers every recursive node, however it was
built.

Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
for performance considerations.
-}
{-# INLINEABLE createMu #-}
createMu ::
    (Typeable symbol, Typeable constraint) => (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint
createMu = dropRedundantMu . createMuDontCleanup
  where
    dropRedundantMu :: Node symbol constraint -> Node symbol constraint
    dropRedundantMu node@(InternedMu mu)
        | RecInt (internedMuId mu) `Set.notMember` freeVars (internedMuBody mu) = internedMuBody mu
        | otherwise = node
    dropRedundantMu node = node

{- | Construct a recursive node, keeping it even when its variable is unused.

Interning a 'Mu' is what assigns the identity its body refers to, so the redundancy check in 'createMu' can only run
afterwards. This is that first half, exported for tests that need to observe a redundant node before it is dropped.
-}
{-# INLINEABLE createMuDontCleanup #-}
createMuDontCleanup ::
    (Typeable symbol, Typeable constraint) => (Node symbol constraint -> Node symbol constraint) -> Node symbol constraint
createMuDontCleanup f =
    internNode $
        UninternedMu
            bodyAtDepth
            (g (RecUnint (numNestedMu bodyAtDepth)))
            g
  where
    g = f . Rec
    bodyAtDepth = g RecDepth

{- | Match on a 'Mu' node

Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
for performance considerations.
-}
{-# INLINEABLE matchMu #-}
matchMu ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> Maybe (Node symbol constraint -> Node symbol constraint)
matchMu (InternedMu mu) = Just $ \n' ->
    if
        | n' == Rec (RecUnint (numNestedMu (internedMuBody mu))) ->
            -- Special case justified by the invariant on 'internedMuShape'
            internedMuShape mu
        | n' == Rec RecDepth ->
            -- Reuse the exact depth probe stored in the interning key. It is
            -- not interchangeable with 'internedMuShape': the distinction is
            -- what keeps an unused nested binder from colliding with a used
            -- binder that has the same ordinary shape.
            internedMuDepthShape mu
        | otherwise ->
            substFree (RecInt (internedMuId mu)) n' (internedMuBody mu)
matchMu _otherwise = Nothing

{- | Substitution

@substFree i n@ will replace all occurrences of @Rec i@ by @n@. We appeal to the uniqueness of node IDs
and assume that all occurrences of @i@ must be free (in other words, that any occurrences of 'Mu' will have a
/different/ identifier).

Postcondition:

> substFree i (Rec i) == id
-}
{-# INLINEABLE substFree #-}
substFree ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    RecNodeId -> Node symbol constraint -> Node symbol constraint -> Node symbol constraint
substFree old new = substFree' (Map.singleton old new)

-- | Generalization of 'substFree' to multiple binders.
{-# INLINEABLE substFree' #-}
substFree' ::
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Map RecNodeId (Node symbol constraint) -> Node symbol constraint -> Node symbol constraint
substFree' env node = case substitutionPlan node of
    SubstitutionPlan f -> f env

-- Substitution internals

{- | A graph rebuild prepared for an environment of recursive substitutions.

This datatype should satisfy two properties for 'substitutionPlan' to work
correctly:

1. Forcing the @SubstitutionPlan@ to WHNF should not result in any recursive calls
   (so that the recursion isn't totally unrolled before memoization can happen).
2. But forcing the /function inside/ the @SubstitutionPlan@ to WHNF /should/
   perform all recursive calls before the function is executed; applying the
   function should not call 'substitutionPlan' again.

Preparing the plan therefore does the expensive traversal once, independently
of the substitution environment. Applying it still rebuilds the graph for each
environment. See @intersect@ for an operation that can avoid an environment
altogether; substitution cannot, because the environment is part of its input.
-}
data SubstitutionPlan symbol constraint a = SubstitutionPlan (Map RecNodeId (Node symbol constraint) -> a)

{- | Commute @[]@ and @SubstitutionPlan@.

Forces all elements in the list
-}
{-# INLINEABLE sequenceSubstitutionPlans #-}
sequenceSubstitutionPlans :: [SubstitutionPlan symbol constraint a] -> SubstitutionPlan symbol constraint [a]
sequenceSubstitutionPlans = SubstitutionPlan . go []
  where
    go ::
        [Map RecNodeId (Node symbol constraint) -> a] ->
        [SubstitutionPlan symbol constraint a] ->
        Map RecNodeId (Node symbol constraint) ->
        [a]
    -- The accumulator is reversed once here rather than on every environment
    -- the resulting function is applied to.
    go acc [] = let fs = reverse acc in \env -> map ($ env) fs
    go acc (SubstitutionPlan !f : fs) = go (f : acc) fs

{- | Extract the shape from a term

Any free variables in the original node become holes that the resulting
plan fills from its environment.

We do not use the pattern synonyms here, because 'substitutionPlan' is used
through 'substFree' to /define/ those pattern synonyms.
-}
genericSubstitutionPlanCache :: TypeableMemoCache
genericSubstitutionPlanCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericSubstitutionPlanCache #-}

substitutionPlan ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Node symbol constraint -> SubstitutionPlan symbol constraint (Node symbol constraint)
{-# INLINEABLE substitutionPlan #-}
substitutionPlan inputNode = memoTypeableWith genericSubstitutionPlanCache onNode inputNode
  where
    onNode :: Node symbol constraint -> SubstitutionPlan symbol constraint (Node symbol constraint)
    onNode n = SubstitutionPlan $
        case n of
            EmptyNode -> const EmptyNode
            InternedNode node -> case sequenceSubstitutionPlans $ map edgeSubstitutionPlan (internedNodeEdges node) of
                SubstitutionPlan !f -> \env -> mkNode (f env)
            InternedMu mu -> case onNode (internedMuBody mu) of
                SubstitutionPlan !f -> \env -> createMu $ \r -> f (Map.insert (RecInt (internedMuId mu)) r env)
            Rec i -> \env -> fromMaybe n (Map.lookup i env)

-- | Prepare substitution for an edge's children.
genericEdgeSubstitutionPlanCache :: TypeableMemoCache
genericEdgeSubstitutionPlanCache = unsafePerformIO newTypeableMemoCache
{-# NOINLINE genericEdgeSubstitutionPlanCache #-}

edgeSubstitutionPlan ::
    forall symbol constraint.
    (Hashable symbol, Typeable symbol, Constraint constraint) =>
    Edge symbol constraint -> SubstitutionPlan symbol constraint (Edge symbol constraint)
{-# INLINEABLE edgeSubstitutionPlan #-}
edgeSubstitutionPlan inputEdge = memoTypeableWith genericEdgeSubstitutionPlanCache onEdge inputEdge
  where
    onEdge :: Edge symbol constraint -> SubstitutionPlan symbol constraint (Edge symbol constraint)
    onEdge e =
        SubstitutionPlan $ case sequenceSubstitutionPlans (map substitutionPlan (edgeChildren e)) of
            SubstitutionPlan !f -> setChildren e . f
