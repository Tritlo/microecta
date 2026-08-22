{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

{- | Interned node and edge representation for the ECTA core.

'DNode' and 'DEdge' are the hash-cons cache keys for an uninterned node and
edge. They are instances of an associated data family, which Haddock cannot
attach documentation to, hence this note.
-}
module Data.ECTA.Internal.ECTA.Type (
    RecNodeId (..),
    Edge (.., Edge),
    pattern DEdge,
    UninternedEdge (..),
    mkEdge,
    emptyEdge,
    edgeChildren,
    edgeEcs,
    edgeSymbol,
    setChildren,
    Node (.., Node, Mu),
    pattern DNode,
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

import Data.Function (on)
import Data.Hashable (Hashable (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import System.IO.Unsafe (unsafePerformIO)

import Data.Interned.Extended.HashTableBased

import Data.ECTA.Internal.Paths
import Data.ECTA.Internal.Term

import Data.Memoization

---------------------------------------------------------------------------------------------

-----------------------------------------------------------------
-------------------------- Mu node table ------------------------
-----------------------------------------------------------------

-- | Internal identifier for references to recursive ECTA nodes.
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

-----------------------------------------------------------------
----------------------------- Edges -----------------------------
-----------------------------------------------------------------

-- | One outgoing alternative of an ECTA node.
data Edge = InternedEdge
    { edgeId :: !Id
    , uninternedEdge :: !UninternedEdge
    }

instance Show Edge where
    show e
        | edgeEcs e == EmptyConstraints = "(Edge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ ")"
        | otherwise = "(mkEdge " ++ show (edgeSymbol e) ++ " " ++ show (edgeChildren e) ++ " " ++ show (edgeEcs e) ++ ")"

-- | Symbol at the root of terms accepted through this edge.
edgeSymbol :: Edge -> Symbol
edgeSymbol = uEdgeSymbol . uninternedEdge

-- | Child automata for this edge.
edgeChildren :: Edge -> [Node]
edgeChildren = uEdgeChildren . uninternedEdge

-- | Equality constraints over paths into 'edgeChildren'.
edgeEcs :: Edge -> EqConstraints
edgeEcs = uEdgeEcs . uninternedEdge

instance Eq Edge where
    (InternedEdge{edgeId = n1}) == (InternedEdge{edgeId = n2}) = n1 == n2

instance Ord Edge where
    compare = compare `on` edgeId

instance Hashable Edge where
    hashWithSalt s e = s `hashWithSalt` (edgeId e)

-----------------------------------------------------------------
------------------------------ Nodes ----------------------------
-----------------------------------------------------------------

-- | Interned recursive node payload.
data InternedMu = MkInternedMu
    { internedMuId :: {-# UNPACK #-} !Id
    -- ^ 'Id' of the node itself
    , internedMuBody :: !Node
    {- ^ The body of the 'Mu'

    Recursive occurrences of this node are

    > Rec (RecInt internedMuId)
    -}
    , internedMuShape :: !Node
    {- ^ The body of the 'Mu', before it was assigned an 'Id'

    Invariant:

    >    substFree (RecInt internedMuId) (Rec (RecUnint (numNestedMu internedMuBody))) internedMuBody
    > == internedMuShape
    -}
    }
    deriving (Show)

-- | Interned non-recursive node payload.
data InternedNode = MkInternedNode
    { internedNodeId :: {-# UNPACK #-} !Id
    -- ^ The 'Id' of the node itself
    , internedNodeEdges :: ![Edge]
    -- ^ All outgoing edges
    , internedNodeNumNestedMu :: !Int
    -- ^ Maximum Mu nesting depth in the term
    , internedNodeFree :: !(Set RecNodeId)
    -- ^ Free variables in the term
    }
    deriving (Show)

-- | ECTA node.
data Node
    = -- | Interned node with one or more outgoing alternatives.
      InternedNode {-# UNPACK #-} !InternedNode
    | -- | Empty language.
      EmptyNode
    | -- | Interned recursive node.
      InternedMu {-# UNPACK #-} !InternedMu
    | -- | Recursive reference used inside a 'Mu'.
      Rec !RecNodeId

instance Eq Node where
    InternedNode l == InternedNode r = internedNodeId l == internedNodeId r
    InternedMu l == InternedMu r = internedMuId l == internedMuId r
    Rec l == Rec r = l == r
    EmptyNode == EmptyNode = True
    _ == _ = False

instance Show Node where
    show (InternedNode node) = "(Node " <> show (internedNodeEdges node) <> ")"
    show EmptyNode = "EmptyNode"
    show (InternedMu mu) = "(Mu " <> show (internedMuId mu) <> " " <> show (internedMuBody mu) <> ")"
    show (Rec n) = "(Rec " <> show n <> ")"

instance Ord Node where
    compare n1 n2 = compare (nodeDescriptorInt n1) (nodeDescriptorInt n2)
      where
        nodeDescriptorInt :: Node -> Int
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

instance Hashable Node where
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
numNestedMu :: Node -> Int
numNestedMu EmptyNode = 0
numNestedMu (InternedNode node) = internedNodeNumNestedMu node
numNestedMu (InternedMu mu) = 1 + numNestedMu (internedMuBody mu)
numNestedMu (Rec _) = 0

{- | Free variables in the term

@O(1)@ in the size of the graph, provided that there are no unbounded Mu chains in the term.
@O(log n)@ in the number of free variables in the graph, which we expect to be orders of magnitude smaller than the
size of the graph (indeed, we don't expect more than a handful).
-}
freeVars :: Node -> Set RecNodeId
freeVars EmptyNode = Set.empty
freeVars (InternedNode node) = internedNodeFree node
freeVars (InternedMu mu) = Set.delete (RecInt (internedMuId mu)) (freeVars (internedMuBody mu))
freeVars (Rec i) = Set.singleton i

----------------------
------ Getters and setters
----------------------

-- | Stable interned identity for non-empty, interned nodes.
nodeIdentity :: Node -> Id
nodeIdentity (InternedMu mu) = internedMuId mu
nodeIdentity (InternedNode node) = internedNodeId node
nodeIdentity (Rec (RecInt i)) = i
nodeIdentity n = error $ "nodeIdentity: unexpected node " <> show n

-- | Replace an edge's children while preserving its symbol and constraints.
setChildren :: Edge -> [Node] -> Edge
setChildren e ns = mkEdge (edgeSymbol e) ns (edgeEcs e)

-----------------------------------------------------------------
------------------------- Interning Nodes -----------------------
-----------------------------------------------------------------

-- | Non-canonical node description used before hash-consing.
data UninternedNode
    = UninternedNode ![Edge]
    | UninternedEmptyNode
    | {- | Recursive node

      The function should be parametric in the Id:

      > substFree i (Rec j) (f i) == f j

      See 'shape' for additional discussion.
      -}
      UninternedMu !(RecNodeId -> Node)

instance Eq UninternedNode where
    UninternedNode es == UninternedNode es' = es == es'
    UninternedEmptyNode == UninternedEmptyNode = True
    UninternedMu mu == UninternedMu mu' = shape mu == shape mu'
    _ == _ = False

instance Hashable UninternedNode where
    hashWithSalt salt = go
      where
        go :: UninternedNode -> Int
        go UninternedEmptyNode = hashWithSalt salt (0 :: Int, ())
        go (UninternedNode es) = hashWithSalt salt (1 :: Int, es)
        go (UninternedMu mu) = hashWithSalt salt (2 :: Int, shape mu)

instance Interned Node where
    type Uninterned Node = UninternedNode
    data Description Node = DNode !UninternedNode
        deriving (Eq)

    describe = DNode

    identify i (UninternedNode es) =
        InternedNode $
            MkInternedNode
                { internedNodeId = i
                , internedNodeEdges = es
                , internedNodeNumNestedMu = maximum (0 : concatMap (map numNestedMu . edgeChildren) es) -- depth is always >= 0
                , internedNodeFree = Set.unions (concatMap (map freeVars . edgeChildren) es)
                }
    identify _ UninternedEmptyNode = EmptyNode
    identify i (UninternedMu n) =
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
                  internedMuShape = shape n
                }

    cache = nodeCache

instance Hashable (Description Node) where
    hashWithSalt salt (DNode node) = salt `hashWithSalt` node

nodeCache :: Cache Node
nodeCache = unsafePerformIO freshCache
{-# NOINLINE nodeCache #-}

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
shape :: (RecNodeId -> Node) -> Node
shape f = f (RecUnint (numNestedMu (f RecDepth)))

-----------------------------------------------------------------
------------------------ Interning Edges ------------------------
-----------------------------------------------------------------

-- | Edge payload before interning.
data UninternedEdge = UninternedEdge
    { uEdgeSymbol :: !Symbol
    , uEdgeChildren :: ![Node]
    , uEdgeEcs :: !EqConstraints
    }
    deriving (Eq, Show)

instance Hashable UninternedEdge where
    hashWithSalt salt (UninternedEdge symbol children ecs) =
        salt `hashWithSalt` symbol `hashWithSalt` children `hashWithSalt` ecs

instance Interned Edge where
    type Uninterned Edge = UninternedEdge
    data Description Edge = DEdge {-# UNPACK #-} !UninternedEdge
        deriving (Eq)

    describe = DEdge

    identify i e = InternedEdge i e

    cache = edgeCache

instance Hashable (Description Edge) where
    hashWithSalt salt (DEdge edge) = salt `hashWithSalt` edge

edgeCache :: Cache Edge
edgeCache = unsafePerformIO freshCache
{-# NOINLINE edgeCache #-}

-----------------------------------------------------------------
----------------------- Smart constructors ----------------------
-----------------------------------------------------------------

-------------------
------ Edge constructors
-------------------

-- | Build or match an unconstrained edge.
pattern Edge :: Symbol -> [Node] -> Edge
pattern Edge s ns <- (InternedEdge _ (UninternedEdge s ns _))
    where
        Edge s ns = intern $ UninternedEdge s ns EmptyConstraints

{-# COMPLETE Edge #-}

-- | Edge that is guaranteed to be removed when a node is built.
emptyEdge :: Edge
emptyEdge = Edge "" [EmptyNode]

isEmptyEdge :: Edge -> Bool
isEmptyEdge (Edge _ ns) = any (== EmptyNode) ns

removeEmptyEdges :: [Edge] -> [Edge]
removeEmptyEdges = filter (not . isEmptyEdge)

-- | Build an edge with equality constraints.
mkEdge :: Symbol -> [Node] -> EqConstraints -> Edge
mkEdge s ns ecs
    | constraintsAreContradictory ecs = emptyEdge
    | otherwise = intern $ UninternedEdge s ns ecs

-------------------
------ Node constructors
-------------------

{-# COMPLETE Node, EmptyNode, Mu, Rec #-}

-- | Build or match a non-empty node from outgoing alternatives.
pattern Node :: [Edge] -> Node
pattern Node es <- (InternedNode (internedNodeEdges -> es))
    where
        Node = mkNode

mkNode :: [Edge] -> Node
mkNode es = case removeEmptyEdges es of
    [] -> EmptyNode
    es' -> intern $ UninternedNode $ Set.toList $ Set.fromList es'

{- | An optimized Node constructor that avoids the interning/preprocessing of the Node constructor
  when nothing changes
-}
modifyNode :: Node -> ([Edge] -> [Edge]) -> Node
modifyNode n@(Node es) f =
    let es' = f es
     in if es' == es
            then
                n
            else
                Node es'
modifyNode n _ = error $ "modifyNode: unexpected node " <> show n

------ Mu

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
> foo (InternedMu mu) = intern $ UninternedMu (f . Rec)

At this point, `intern` will call `shape (f . Rec)`, which will call `f . Rec` twice: once with `RecDepth` to compute
the depth, and then once again with that depth to substitute a placeholder. Both of these special cases will use
'internedMuShape' (and moreover, the depth calculation on 'internedMuShape' is @O(1)@).
-}
pattern Mu :: (Node -> Node) -> Node
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
createMu :: (Node -> Node) -> Node
createMu = dropRedundantMu . createMuDontCleanup
  where
    dropRedundantMu :: Node -> Node
    dropRedundantMu node@(InternedMu mu)
        | RecInt (internedMuId mu) `Set.notMember` freeVars (internedMuBody mu) = internedMuBody mu
        | otherwise = node
    dropRedundantMu node = node

{- | Construct a recursive node, keeping it even when its variable is unused.

Interning a 'Mu' is what assigns the identity its body refers to, so the redundancy check in 'createMu' can only run
afterwards. This is that first half, exported for tests that need to observe a redundant node before it is dropped.
-}
createMuDontCleanup :: (Node -> Node) -> Node
createMuDontCleanup f = intern $ UninternedMu (f . Rec)

{- | Match on a 'Mu' node

Implementation note: 'createMu' and 'matchMu' interact in non-trivial ways; see docs of the 'Mu' pattern synonym
for performance considerations.
-}
matchMu :: Node -> Maybe (Node -> Node)
matchMu (InternedMu mu) = Just $ \n' ->
    if
        | n' == Rec (RecUnint (numNestedMu (internedMuBody mu))) ->
            -- Special case justified by the invariant on 'internedMuShape'
            internedMuShape mu
        | n' == Rec RecDepth ->
            -- The use of 'RecDepth' implies that we are computing a depth:
            --
            -- >    numNestedMu (substFree (internedMuId mu) (Rec RecDepth)) (internedMuBody mu))
            -- >      -- { depth calculation does not depend on choice of variable }
            -- > == numNestedMu (substFree (internedMuId mu) Rec (RecUnint (numNestedMu (internedMuBody mu)))) (internedMuBody mu))
            -- >      -- { invariant of internedMuShape }
            -- > == numNestedMu internedMuShape
            internedMuShape mu
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
substFree :: RecNodeId -> Node -> Node -> Node
substFree old new = substFree' (Map.singleton old new)

-- | Generalization of 'substFree' to multiple binders.
substFree' :: Map RecNodeId Node -> Node -> Node
substFree' env node = case template node of
    Template f -> f env

------ Substitution internals

{- | The template of a something is that something with holes for as-yet unknown 'Id's

This datatype should satisfy two properties for 'template' to work correctly:

1. Forcing the @Template@ to WHNF should not result in any recursive calls
   (so that the recursion isn't totally unrolled before memoization can happen).
2. But forcing the /function inside/ the @Template@ to WHNF /should/ result in all recursive calls to happen,
   (/before/ the function is executed: executing the function should /not/ cause further calls to 'template').

The idea here is that a function returning a @Template@, the application of that @Template@ should not result in
further recursive calls to that function, so that any expensive computation done by that function is not repeated,
but is done independently of the environment (the 'Map') that we provide to the @Template@. Put another way: the
function can be memoized independently of that environment. For substitution this may not matter very much, but for
other functions it could. Note however that the resulting @Template@ does build the graph on each invocation; this
may still be prohibitively expensive. See @intersect@ for an example of how we can avoid an environment altogether.
(This is not an option for substitution of course, where the environment is part of the API of the function.)
-}
data Template a = Template (Map RecNodeId Node -> a)

{- | Commute @[]@ and @Template@

Forces all elements in the list
-}
sequenceTemplate :: [Template a] -> Template [a]
sequenceTemplate = Template . go []
  where
    go :: [Map RecNodeId Node -> a] -> [Template a] -> Map RecNodeId Node -> [a]
    -- The accumulator is reversed once here rather than on every environment
    -- the resulting function is applied to.
    go acc [] = let fs = reverse acc in \env -> map ($ env) fs
    go acc (Template !f : fs) = go (f : acc) fs

{- | Extract the shape from a term

Somewhat serendipitously (or does this point to some deeper truth?) this also serves as a definition of substitution:
any free variables in the original node will become " holes " in the @Template@.

We do not use the pattern synonyms here, because 'template' is used (through 'substFree') to /define/ those
pattern synonyms.
-}
template :: Node -> Template Node
{-# NOINLINE template #-}
template = memo (NameTag "template") onNode
  where
    onNode :: Node -> Template Node
    onNode n = Template $
        case n of
            EmptyNode -> \_ -> EmptyNode
            InternedNode node -> case sequenceTemplate $ map templateEdge (internedNodeEdges node) of
                Template !f -> \env -> mkNode (f env)
            InternedMu mu -> case onNode (internedMuBody mu) of
                Template !f -> \env -> createMu $ \r -> f (Map.insert (RecInt (internedMuId mu)) r env)
            Rec i -> \env -> fromMaybe n (Map.lookup i env)

-- | Internal auxiliary to 'template'
templateEdge :: Edge -> Template Edge
{-# NOINLINE templateEdge #-}
templateEdge = memo (NameTag "templateEdge") onEdge
  where
    onEdge :: Edge -> Template Edge
    onEdge e =
        Template $ case sequenceTemplate (map template (edgeChildren e)) of
            Template !f -> setChildren e . f
