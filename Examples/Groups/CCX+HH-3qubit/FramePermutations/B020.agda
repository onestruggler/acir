{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B020 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE01043 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s6) ≈ p (s6 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s6) (s6 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01044 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1) ≈ p (s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1) (s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01045 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1) (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01046 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01047 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01048 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01049 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2) ≈ p (s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2) (s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01050 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2) (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01051 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01052 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01053 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3) ≈ p (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3) (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01054 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s3) (s3 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01055 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01056 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4) ≈ p (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4) (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01057 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01058 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s6 • s5) (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01059 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1) ≈ p (s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1) (s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01060 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1) (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01061 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01062 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01063 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01064 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2) ≈ p (s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2) (s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01065 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2) (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01066 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01067 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01068 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3) ≈ p (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3) (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01069 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s3) (s3 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01070 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01071 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4) ≈ p (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4) (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01072 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4) (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01073 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5) ≈ p (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5) (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01074 where

  proved : p (s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s0 • s1 • s0) (s0 • s1 • s0 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01075 where

  proved : p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01076 where

  proved : p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01077 where

  proved : p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01078 where

  proved : p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01079 where

  proved : p (s1 • s2 • s1 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s2 • s3 • s2) (s2 • s3 • s2 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01080 where

  proved : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01081 where

  proved : p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01082 where

  proved : p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01083 where

  proved : p (s1 • s2 • s1 • s4) ≈ p (s4 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s4) (s4 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01084 where

  proved : p (s1 • s2 • s1 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s4 • s5 • s4) (s4 • s5 • s4 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01085 where

  proved : p (s1 • s2 • s1 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01086 where

  proved : p (s1 • s2 • s1 • s5) ≈ p (s5 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s5) (s5 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01087 where

  proved : p (s1 • s2 • s1 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s5 • s6 • s5) (s5 • s6 • s5 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01088 where

  proved : p (s1 • s2 • s1 • s6) ≈ p (s6 • s1 • s2 • s1)
  proved = checked (s1 • s2 • s1 • s6) (s6 • s1 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01089 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s0) (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01090 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01091 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01092 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01093 where

  proved : p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
