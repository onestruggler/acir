{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01342 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; suc ; zero ; module Eq)
open K

proved : p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
proved = checked (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
