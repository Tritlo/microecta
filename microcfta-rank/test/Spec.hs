{- | The contract of ranked languages: every rank decodes to its member, the
sizes and the size-major order agree with an enumeration, the samplers give
the distribution of the plan, and shrinking gives smaller members.
-}
module Main (main) where

import Test.Hspec (hspec)

import qualified Data.CFTA.RankedSpec

main :: IO ()
main = hspec Data.CFTA.RankedSpec.spec
