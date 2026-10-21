{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B025 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE01312 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01313 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01314 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01315 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s6 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s6 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01316 where

  proved : p (s1 • s2 • s1 • s1 • s2 • s3 • s2 • s1) ≈ p (s3 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s1 • s2 • s3 • s2 • s1) (s3 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01317 where

  proved : p (s1 • s2 • s1 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s3 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s3 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01318 where

  proved : p (s1 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01319 where

  proved : p (s1 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01320 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s4 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s4 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01321 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s4 • s5 • s4 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s4 • s5 • s4 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01322 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01323 where

  proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s5 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s5 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01324 where

  proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s5 • s6 • s5 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s5 • s6 • s5 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01325 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s6 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s6 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01326 where

  proved : p (s2 • s3 • s2 • s2 • s3 • s4 • s3 • s2) ≈ p (s4 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s2 • s3 • s4 • s3 • s2) (s4 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01327 where

  proved : p (s2 • s3 • s2 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s4 • s5 • s4 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s4 • s5 • s4 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01328 where

  proved : p (s2 • s3 • s2 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01329 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s5 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s5 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01330 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s5 • s6 • s5 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s5 • s6 • s5 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01331 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s6 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s6 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01332 where

  proved : p (s3 • s4 • s3 • s3 • s4 • s5 • s4 • s3) ≈ p (s5 • s3 • s4 • s3)
  proved = checked (s3 • s4 • s3 • s3 • s4 • s5 • s4 • s3) (s5 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01333 where

  proved : p (s3 • s4 • s3 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s5 • s6 • s5 • s3 • s4 • s3)
  proved = checked (s3 • s4 • s3 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s5 • s6 • s5 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01334 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s6 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s6 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01335 where

  proved : p (s4 • s5 • s4 • s4 • s5 • s6 • s5 • s4) ≈ p (s6 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s4 • s5 • s6 • s5 • s4) (s6 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01336 where

  proved : p (s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01337 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01338 where

  proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01339 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01340 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01341 where

  proved : p (s2 • s3 • s2 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s0 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01342 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01343 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01344 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01345 where

  proved : p (s3 • s4 • s3 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s3)
  proved = checked (s3 • s4 • s3 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01346 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01347 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01348 where

  proved : p (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01349 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01350 where

  proved : p (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01351 where

  proved : p (s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01352 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01353 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01354 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01355 where

  proved : p (s3 • s4 • s3 • s1 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s3 • s4 • s3)
  proved = checked (s3 • s4 • s3 • s1 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01356 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s1 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s1 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01357 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s1 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s1 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01358 where

  proved : p (s4 • s5 • s4 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01359 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01360 where

  proved : p (s5 • s6 • s5 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s5 • s6 • s5)
  proved = checked (s5 • s6 • s5 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s5 • s6 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01361 where

  proved : p (s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s3)
  proved = checked (s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01362 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01363 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01364 where

  proved : p (s4 • s5 • s4 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4 • s5 • s4)
  proved = checked (s4 • s5 • s4 • s2 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01365 where

  proved : p (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4)
  proved = checked (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
