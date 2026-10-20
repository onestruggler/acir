{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00229 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X56 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00194 as E

proved : p (s3) • X56 ≈ X56 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
