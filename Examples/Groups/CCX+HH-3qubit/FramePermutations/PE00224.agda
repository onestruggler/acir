{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00224 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s3 ; s4 ; s5 ; s6 ; suc ; zero ; module Eq)
open K

proved : p (s3 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
proved = checked (s3 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
