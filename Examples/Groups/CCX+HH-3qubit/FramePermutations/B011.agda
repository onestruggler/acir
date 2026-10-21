{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B011 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE00595 where

  proved : p (s6 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00596 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00597 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00598 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00599 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00600 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00601 where

  proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00602 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00603 where

  proved : p (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00604 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00605 where

  proved : p (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00606 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00607 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00608 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00609 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00610 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00611 where

  proved : p (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00612 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00613 where

  proved : p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00614 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00615 where

  proved : p (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00616 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00617 where

  proved : p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00618 where

  proved : p (s2 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s4)
  proved = checked (s2 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00619 where

  proved : p (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
  proved = checked (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00620 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s4)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00621 where

  proved : p (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00622 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00623 where

  proved : p (s5 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00624 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00625 where

  proved : p (s6 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00626 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00627 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00628 where

  proved : p (s2 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s2 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00629 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00630 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00631 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00632 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00633 where

  proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00634 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00635 where

  proved : p (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00636 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00637 where

  proved : p (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00638 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00639 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00640 where

  proved : p (s2 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s2 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00641 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00642 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00643 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00644 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00645 where

  proved : p (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00646 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00647 where

  proved : p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00648 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
