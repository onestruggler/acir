{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00216 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; p ; s3 ; s4 ; suc ; zero ; module Eq)
open K

proved : p (s3 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s4)
proved = checked (s3 • s3 • s4 • s3) (s3 • s4 • s3 • s4)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
