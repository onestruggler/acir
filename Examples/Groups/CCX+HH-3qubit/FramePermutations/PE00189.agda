{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00189 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s4 ; s5 ; s6 ; suc ; zero ; module Eq)
open K

proved : p (s5 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s5)
proved = checked (s5 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s5)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
