{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B022 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE01145 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01146 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4) ≈ p (s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4) (s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01147 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4 • s5 • s4) (s4 • s5 • s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01148 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s5) ≈ p (s5 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  proved = checked (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s5) (s5 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01149 where

  proved : p (s2 • s3 • s2 • s0) ≈ p (s0 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s0) (s0 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01150 where

  proved : p (s2 • s3 • s2 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01151 where

  proved : p (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01152 where

  proved : p (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01153 where

  proved : p (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01154 where

  proved : p (s2 • s3 • s2 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s1 • s2 • s1) (s1 • s2 • s1 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01155 where

  proved : p (s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01156 where

  proved : p (s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01157 where

  proved : p (s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01158 where

  proved : p (s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s3 • s4 • s3) (s3 • s4 • s3 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01159 where

  proved : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01160 where

  proved : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01161 where

  proved : p (s2 • s3 • s2 • s5) ≈ p (s5 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s5) (s5 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01162 where

  proved : p (s2 • s3 • s2 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s5 • s6 • s5) (s5 • s6 • s5 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01163 where

  proved : p (s2 • s3 • s2 • s6) ≈ p (s6 • s2 • s3 • s2)
  proved = checked (s2 • s3 • s2 • s6) (s6 • s2 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01164 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s0) ≈ p (s0 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s0) (s0 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01165 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01166 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01167 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01168 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01169 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1) (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01170 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01171 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01172 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01173 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s3) ≈ p (s3 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s3) (s3 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01174 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01175 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01176 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s4) ≈ p (s4 • s5 • s4 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s4) (s4 • s5 • s4 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01177 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01178 where

  proved : p (s2 • s3 • s4 • s3 • s2 • s6) ≈ p (s6 • s2 • s3 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s3 • s2 • s6) (s6 • s2 • s3 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01179 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0) ≈ p (s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0) (s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01180 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01181 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01182 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01183 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01184 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1) (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01185 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01186 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01187 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01188 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3) ≈ p (s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3) (s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01189 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3) ≈ p (s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3) (s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01190 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01191 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4) ≈ p (s4 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4) (s4 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01192 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4) ≈ p (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s4 • s5 • s6 • s5 • s4) (s4 • s5 • s6 • s5 • s4 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01193 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s5 • s6 • s5) ≈ p (s5 • s6 • s5 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s5 • s6 • s5) (s5 • s6 • s5 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01194 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0) ≈ p (s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0) (s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01195 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s1 • s0) (s0 • s1 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01196 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01197 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE01198 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
