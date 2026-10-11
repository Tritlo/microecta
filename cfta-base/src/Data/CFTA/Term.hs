{-# LANGUAGE DeriveTraversable #-}

{- | Terms with one constructor for each small arity.

A leaf and a term with one, two, or three children hold their children in
constructor fields, and a term with four or more children holds them in a
'Seq'. A path reads a subterm with one field read or one 'Seq.lookup' for
each child index. A term with @n@ children holds them at the indexes @0@ to
@n - 1@. Most modules build terms through 'Node', 'fromAssocs', and
'traverseNode', and read children through 'child', 'childAt', 'subForest',
and 'arity'. Code that builds terms of a known arity in a hot loop uses the
constructors directly, so that no list of children is built. 'Many' must hold
four or more children.

The 'Ord' and 'Hashable' instances agree with the instances of
'Tree.Tree' on the same term: 'Ord' compares the symbol, then the children in
index order, and 'Hashable' hashes the symbol, then the children, then their
number. So a set or a hash set of terms keeps the order it had with
'Tree.Tree'. 'Many' holds four or more children, so the derived 'Eq' is
equality of the symbol and the child lists.
-}
module Data.CFTA.Term (
    Term (Leaf, One, Two, Three, Many, Node),
    rootLabel,
    subForest,
    arity,
    child,
    childAt,
    adjustChild,
    fromAssocs,
    traverseNode,
    flatten,
    foldTree,
    fromRoseTree,
    toRoseTree,
) where

import Data.Foldable (toList)
import Data.Hashable (Hashable (..))
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Tree as Tree

-- | A term: a symbol with its children, in a constructor chosen by the arity.
data Term symbol
    = Leaf symbol
    | One symbol (Term symbol)
    | Two symbol (Term symbol) (Term symbol)
    | Three symbol (Term symbol) (Term symbol) (Term symbol)
    | -- | Four or more children.
      Many symbol !(Seq (Term symbol))
    deriving (Eq, Functor, Foldable, Traversable)

instance (Ord symbol) => Ord (Term symbol) where
    compare left right = compare (rootLabel left) (rootLabel right) <> children 0
      where
        shared = min (arity left) (arity right)
        children index
            | index < shared = compare (childAt index left) (childAt index right) <> children (index + 1)
            | otherwise = compare (arity left) (arity right)

-- | A term shows as 'Node' builds it: the symbol, then the children as a list.
instance (Show symbol) => Show (Term symbol) where
    showsPrec d term =
        showParen (d > 10) $ showString "Node " . showsPrec 11 (rootLabel term) . showChar ' ' . showsPrec 11 (subForest term)

instance (Hashable symbol) => Hashable (Term symbol) where
    hashWithSalt salt (Leaf symbol) = hashWithSalt (hashWithSalt salt symbol) (0 :: Int)
    hashWithSalt salt (One symbol first) = hashWithSalt (hashWithSalt (hashWithSalt salt symbol) first) (1 :: Int)
    hashWithSalt salt (Two symbol first second) =
        hashWithSalt (hashWithSalt (hashWithSalt (hashWithSalt salt symbol) first) second) (2 :: Int)
    hashWithSalt salt (Three symbol first second third) =
        hashWithSalt (hashWithSalt (hashWithSalt (hashWithSalt (hashWithSalt salt symbol) first) second) third) (3 :: Int)
    hashWithSalt salt (Many symbol children) =
        hashWithSalt (foldl' hashWithSalt (hashWithSalt salt symbol) children) (Seq.length children)

{-# COMPLETE Node #-}

-- 'Node' inlines as written, so that 'unNode' inlines in the module of the match (see 'unNode').
{-# INLINE Node #-}

{- | A term with its children as a list, as 'Tree.Node' gives them. Building
a term from a list gives the children the indexes @0@ to @n - 1@. It
evaluates the spine of the list but not the children, as 'Tree.Node' does,
so a reader of the root symbol does not build the subterms.
-}
pattern Node :: symbol -> [Term symbol] -> Term symbol
pattern Node symbol children <- (unNode -> (symbol, children))
  where
    Node symbol [] = Leaf symbol
    Node symbol [first] = One symbol first
    Node symbol [first, second] = Two symbol first second
    Node symbol [first, second, third] = Three symbol first second third
    Node symbol children = Many symbol (Seq.fromList children)

{- | The symbol and the children of a term.

'unNode' inlines only in the last phase of the simplifier. Inlined earlier,
a match on 'Node' becomes one branch per constructor that jumps to the
body of the match. In that shape, GHC can keep a literal symbol of the
match, such as @"int-0"@, inside the body, and then each match interns the
text of the literal again. Inlined last, GHC first moves each literal to a
top-level constant. The INLINE pragma of 'Node' keeps the call of
'unNode' in the matcher, so that the phase applies in the module of the
match and not in this module.
-}
unNode :: Term symbol -> (symbol, [Term symbol])
unNode (Leaf symbol) = (symbol, [])
unNode (One symbol first) = (symbol, [first])
unNode (Two symbol first second) = (symbol, [first, second])
unNode (Three symbol first second third) = (symbol, [first, second, third])
unNode (Many symbol children) = (symbol, toList children)
{-# INLINE [0] unNode #-}

-- | The placeholder of a child that a builder has not written.
unfilled :: a
unfilled = error "Data.CFTA.Term: a builder left a child unfilled"

-- | The symbol at the root of a term.
rootLabel :: Term symbol -> symbol
rootLabel (Leaf symbol) = symbol
rootLabel (One symbol _) = symbol
rootLabel (Two symbol _ _) = symbol
rootLabel (Three symbol _ _ _) = symbol
rootLabel (Many symbol _) = symbol

-- | The children of a term in index order.
subForest :: Term symbol -> [Term symbol]
subForest (Leaf _) = []
subForest (One _ first) = [first]
subForest (Two _ first second) = [first, second]
subForest (Three _ first second third) = [first, second, third]
subForest (Many _ children) = toList children

-- | The number of children of a term.
arity :: Term symbol -> Int
arity (Leaf _) = 0
arity (One _ _) = 1
arity Two{} = 2
arity Three{} = 3
arity (Many _ children) = Seq.length children

-- | The child at an index, when the term has that many children.
child :: Int -> Term symbol -> Maybe (Term symbol)
child 0 (One _ first) = Just first
child 0 (Two _ first _) = Just first
child 1 (Two _ _ second) = Just second
child 0 (Three _ first _ _) = Just first
child 1 (Three _ _ second _) = Just second
child 2 (Three _ _ _ third) = Just third
child index (Many _ children) = Seq.lookup index children
child _ _ = Nothing

-- | The child at an index. The caller has checked that the term has that many children.
childAt :: Int -> Term symbol -> Term symbol
childAt 0 (One _ first) = first
childAt 0 (Two _ first _) = first
childAt 1 (Two _ _ second) = second
childAt 0 (Three _ first _ _) = first
childAt 1 (Three _ _ second _) = second
childAt 2 (Three _ _ _ third) = third
childAt index (Many _ children) = Seq.index children index
childAt _ _ = error "Data.CFTA.Term.childAt: the term has no such child"

-- | Apply a function to the child at an index, when the term has that many children.
adjustChild :: (Term symbol -> Term symbol) -> Int -> Term symbol -> Term symbol
adjustChild f 0 (One symbol first) = One symbol (f first)
adjustChild f 0 (Two symbol first second) = Two symbol (f first) second
adjustChild f 1 (Two symbol first second) = Two symbol first (f second)
adjustChild f 0 (Three symbol first second third) = Three symbol (f first) second third
adjustChild f 1 (Three symbol first second third) = Three symbol first (f second) third
adjustChild f 2 (Three symbol first second third) = Three symbol first second (f third)
adjustChild f index (Many symbol children) = Many symbol (Seq.adjust f index children)
adjustChild _ _ term = term

{- | A term from its arity and its children keyed by child index. Each index
from @0@ to @arity - 1@ appears once in the list.
-}
fromAssocs :: symbol -> Int -> [(Int, Term symbol)] -> Term symbol
fromAssocs symbol size assocs = case assocs of
    [] -> Leaf symbol
    [(_, first)] -> One symbol first
    [(0, first), (_, second)] -> Two symbol first second
    [(_, second), (_, first)] -> Two symbol first second
    [(0, first), (1, second), (_, third)] -> Three symbol first second third
    [(0, first), (_, third), (_, second)] -> Three symbol first second third
    [(1, second), (0, first), (_, third)] -> Three symbol first second third
    [(1, second), (_, third), (_, first)] -> Three symbol first second third
    [(_, third), (0, first), (_, second)] -> Three symbol first second third
    [(_, third), (_, second), (_, first)] -> Three symbol first second third
    _ ->
        Many symbol $ foldl' (\children (index, term) -> Seq.update index term children) (Seq.replicate size unfilled) assocs

{- | The term of a symbol and of an action on each child, run from left to
right. A term with up to three children gets them without a list.
-}
traverseNode :: (Applicative f) => (child -> f (Term symbol)) -> symbol -> [child] -> f (Term symbol)
traverseNode f symbol children = case children of
    [] -> pure $ Leaf symbol
    [first] -> One symbol <$> f first
    [first, second] -> Two symbol <$> f first <*> f second
    [first, second, third] -> Three symbol <$> f first <*> f second <*> f third
    _ -> Many symbol . Seq.fromList <$> traverse f children
{-# INLINE traverseNode #-}

-- | The symbols of a term in preorder, as 'Tree.flatten' gives them.
flatten :: Term symbol -> [symbol]
flatten term = go term []
  where
    go (Leaf symbol) rest = symbol : rest
    go (One symbol first) rest = symbol : go first rest
    go (Two symbol first second) rest = symbol : go first (go second rest)
    go (Three symbol first second third) rest = symbol : go first (go second (go third rest))
    go (Many symbol children) rest = symbol : foldr go rest children

-- | Fold a term bottom up, as 'Tree.foldTree' does.
foldTree :: (symbol -> [a] -> a) -> Term symbol -> a
foldTree f = go
  where
    go term = f (rootLabel term) (map go (subForest term))

-- | The term of a rose tree.
fromRoseTree :: Tree.Tree symbol -> Term symbol
fromRoseTree = Tree.foldTree Node

-- | The rose tree of a term, for 'Tree.drawTree' and other users of 'Tree.Tree'.
toRoseTree :: Term symbol -> Tree.Tree symbol
toRoseTree = foldTree Tree.Node
