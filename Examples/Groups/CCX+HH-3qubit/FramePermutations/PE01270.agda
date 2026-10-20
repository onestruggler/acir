{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01270 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s0 ; s1 ; s4 ; s5 ; s6 ; suc ; zero ; module Eq)
open K

proved : p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
proved = checked (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s0) (s0 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
