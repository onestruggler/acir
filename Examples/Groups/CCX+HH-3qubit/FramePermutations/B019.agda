{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B019 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE00989 where

  proved : p (s0 • s1 • s0 • s3) ≈ p (s3 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s3) (s3 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00990 where

  proved : p (s0 • s1 • s0 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s3 • s4 • s3) (s3 • s4 • s3 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00991 where

  proved : p (s0 • s1 • s0 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00992 where

  proved : p (s0 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00993 where

  proved : p (s0 • s1 • s0 • s4) ≈ p (s4 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s4) (s4 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00994 where

  proved : p (s0 • s1 • s0 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s4 • s5 • s4) (s4 • s5 • s4 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00995 where

  proved : p (s0 • s1 • s0 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00996 where

  proved : p (s0 • s1 • s0 • s5) ≈ p (s5 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s5) (s5 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00997 where

  proved : p (s0 • s1 • s0 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s5 • s6 • s5) (s5 • s6 • s5 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00998 where

  proved : p (s0 • s1 • s0 • s6) ≈ p (s6 • s0 • s1 • s0)
  proved = checked (s0 • s1 • s0 • s6) (s6 • s0 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00999 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s1) ≈ p (s1 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s1) (s1 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01000 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01001 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01002 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01003 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01004 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s2) (s2 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01005 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01006 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01007 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01008 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s4) ≈ p (s4 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s4) (s4 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01009 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s4) (s4 • s5 • s4 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01010 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01011 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s5) ≈ p (s5 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s5) (s5 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01012 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s5 • s6 • s5) (s5 • s6 • s5 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01013 where

  proved : p (s0 • s1 • s2 • s1 • s0 • s6) ≈ p (s6 • s0 • s1 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s1 • s0 • s6) (s6 • s0 • s1 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01014 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1) ≈ p (s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1) (s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01015 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1) (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01016 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01017 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01018 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01019 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2) ≈ p (s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2) (s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01020 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2) (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01021 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01022 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01023 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s3 • s4 • s3) (s3 • s4 • s3 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01024 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01025 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01026 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s5) ≈ p (s5 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s5) (s5 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01027 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s5 • s6 • s5) (s5 • s6 • s5 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01028 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s6) ≈ p (s6 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s6) (s6 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01029 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1) ≈ p (s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1) (s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01030 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1) (s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01031 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01032 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01033 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01034 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2) ≈ p (s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2) (s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01035 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2) (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01036 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01037 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01038 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3) ≈ p (s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3) (s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01039 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01040 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01041 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s4) (s4 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01042 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
