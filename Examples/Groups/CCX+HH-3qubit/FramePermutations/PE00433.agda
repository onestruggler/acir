{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00433 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; suc ; zero ; module Eq)
open K

proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s4)
proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s4)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
