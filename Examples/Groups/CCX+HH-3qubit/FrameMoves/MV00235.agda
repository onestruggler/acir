{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X57 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00200 as E

proved : p (s3) • X57 ≈ X57 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
