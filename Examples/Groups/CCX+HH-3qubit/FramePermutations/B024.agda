{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B024 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE01253 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5) ≈ p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5) (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01254 where

  proved : p (s4 • s5 • s4 • s0) ≈ p (s0 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s0) (s0 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01255 where

  proved : p (s4 • s5 • s4 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s0 • s1 • s0) (s0 • s1 • s0 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01256 where

  proved : p (s4 • s5 • s4 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01257 where

  proved : p (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01258 where

  proved : p (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01259 where

  proved : p (s4 • s5 • s4 • s1) ≈ p (s1 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s1) (s1 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01260 where

  proved : p (s4 • s5 • s4 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s1 • s2 • s1) (s1 • s2 • s1 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01261 where

  proved : p (s4 • s5 • s4 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01262 where

  proved : p (s4 • s5 • s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01263 where

  proved : p (s4 • s5 • s4 • s2) ≈ p (s2 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s2) (s2 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01264 where

  proved : p (s4 • s5 • s4 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01265 where

  proved : p (s4 • s5 • s4 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01266 where

  proved : p (s4 • s5 • s4 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s3 • s4 • s3) (s3 • s4 • s3 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01267 where

  proved : p (s4 • s5 • s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01268 where

  proved : p (s4 • s5 • s4 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s5 • s6 • s5) (s5 • s6 • s5 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01269 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s0) ≈ p (s0 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s0) (s0 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01270 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s0) (s0 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01271 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01272 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01273 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01274 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s1) ≈ p (s1 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s1) (s1 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01275 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s1) (s1 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01276 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01277 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01278 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s2) ≈ p (s2 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s2) (s2 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01279 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01280 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01281 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s3 • s4 • s3) (s3 • s4 • s3 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01282 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01283 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s5) ≈ p (s5 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s5) (s5 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01284 where

  proved : p (s5 • s6 • s5 • s0) ≈ p (s0 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s0) (s0 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01285 where

  proved : p (s5 • s6 • s5 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s0 • s1 • s0) (s0 • s1 • s0 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01286 where

  proved : p (s5 • s6 • s5 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01287 where

  proved : p (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01288 where

  proved : p (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01289 where

  proved : p (s5 • s6 • s5 • s1) ≈ p (s1 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s1) (s1 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01290 where

  proved : p (s5 • s6 • s5 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s1 • s2 • s1) (s1 • s2 • s1 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01291 where

  proved : p (s5 • s6 • s5 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01292 where

  proved : p (s5 • s6 • s5 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01293 where

  proved : p (s5 • s6 • s5 • s2) ≈ p (s2 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s2) (s2 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01294 where

  proved : p (s5 • s6 • s5 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s2 • s3 • s2) (s2 • s3 • s2 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01295 where

  proved : p (s5 • s6 • s5 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01296 where

  proved : p (s5 • s6 • s5 • s3) ≈ p (s3 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s3) (s3 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01297 where

  proved : p (s5 • s6 • s5 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01298 where

  proved : p (s5 • s6 • s5 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s4 • s5 • s4) (s4 • s5 • s4 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01301 where

  proved : p (s0 • s1 • s0 • s0 • s1 • s2 • s1 • s0) ≈ p (s2 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s0 • s1 • s2 • s1 • s0) (s2 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01302 where

  proved : p (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s2 • s3 • s2 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s2 • s3 • s2 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01303 where

  proved : p (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01304 where

  proved : p (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01305 where

  proved : p (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01306 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s3 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01307 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01308 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01309 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01310 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01311 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
