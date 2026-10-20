{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01286 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s0 ; s1 ; s2 ; s5 ; s6 ; suc ; zero ; module Eq)
open K

proved : p (s5 • s6 • s5 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s5 • s6 • s5)
proved = checked (s5 • s6 • s5 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s5 • s6 • s5)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
