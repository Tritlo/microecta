{- | Explicit patterns for concrete terms and ECTA languages.

The patterns come from "Data.CFTA.Template". 'termsMatching' restricts
the shared graph and then reduces the equality constraints, so a 'Hole' at a
constrained position can be narrowed by a concrete pattern at an equal one.
-}
module Data.CFTA.Equality.Template (
    Template (..),
    matchesTemplate,
    termsMatching,
) where

import Data.Hashable (Hashable)
import Type.Reflection (Typeable)

import Data.CFTA.Equality.Node (Node, fromInterned, toInterned)
import Data.CFTA.Equality.Operations (reducePartially)
import Data.CFTA.Template (Template (..), matchesTemplate, restrict)

-- | Keep exactly the terms in a node that match a template.
termsMatching :: (Hashable symbol, Typeable symbol) => Template symbol -> Node symbol -> Node symbol
termsMatching Hole = id
termsMatching (AnyPrefix []) = id
termsMatching template = reducePartially . fromInterned . restrict template . toInterned
