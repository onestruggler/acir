{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B012 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE00649 where

  proved : p (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00650 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00651 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00652 where

  proved : p (s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
  proved = checked (s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00653 where

  proved : p (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
  proved = checked (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00654 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00655 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00656 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00657 where

  proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00658 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00659 where

  proved : p (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00660 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00661 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00662 where

  proved : p (s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s6)
  proved = checked (s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00663 where

  proved : p (s6 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
  proved = checked (s6 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00664 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00665 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00666 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00667 where

  proved : p (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00668 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00669 where

  proved : p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00670 where

  proved : p (s6 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00671 where

  proved : p (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00672 where

  proved : p (s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00673 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00674 where

  proved : p (s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
  proved = checked (s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00675 where

  proved : p (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
  proved = checked (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00676 where

  proved : p (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s3 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00677 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00678 where

  proved : p (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00679 where

  proved : p (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00680 where

  proved : p (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00681 where

  proved : p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00682 where

  proved : p (s0 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00686 where

  proved : p (s2 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s4)
  proved = checked (s2 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00687 where

  proved : p (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s2)
  proved = checked (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00688 where

  proved : p (s5 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00689 where

  proved : p (s5 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00690 where

  proved : p (s6 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s6)
  proved = checked (s6 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00691 where

  proved : p (s6 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s6)
  proved = checked (s6 • s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00692 where

  proved : p (s0 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s0 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00693 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00694 where

  proved : p (s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00695 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0 • s1)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00696 where

  proved : p (s2 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s2 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00697 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s2)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00698 where

  proved : p (s4 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00699 where

  proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s0 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00700 where

  proved : p (s5 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s5)
  proved = checked (s5 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00701 where

  proved : p (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
