{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01113 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s1 ; s2 ; s3 ; s4 ; suc ; zero ; module Eq)
open K

proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s3) ≈ p (s3 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
proved = checked (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s3) (s3 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
