{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00188 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00153 as E

proved : p (s3) • X35 ≈ X45 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
