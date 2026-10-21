{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.B007 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; checked ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; suc ; zero)
open K

module PE00378 where

  proved : p (s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00379 where

  proved : p (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00380 where

  proved : p (s5 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00381 where

  proved : p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00382 where

  proved : p (s6 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00383 where

  proved : p (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00384 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00385 where

  proved : p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s0)
  proved = checked (s3 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00386 where

  proved : p (s1 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s2 • s3 • s2 • s3 • s4 • s3)
  proved = checked (s1 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s2 • s3 • s2 • s3 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00387 where

  proved : p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  proved = checked (s3 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s3 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00390 where

  proved : p (s3 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s3 • s4)
  proved = checked (s3 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s1 • s2 • s3 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00391 where

  proved : p (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s3 • s2 • s1 • s3)
  proved = checked (s4 • s3 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s3 • s2 • s1 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00392 where

  proved : p (s5 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00393 where

  proved : p (s5 • s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s5)
  proved = checked (s5 • s3 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00394 where

  proved : p (s6 • s1 • s2 • s3 • s2 • s3 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3 • s6)
  proved = checked (s6 • s1 • s2 • s3 • s2 • s3 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00395 where

  proved : p (s6 • s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s6)
  proved = checked (s6 • s3 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00396 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00397 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s0)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00398 where

  proved : p (s1 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s1 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00399 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00400 where

  proved : p (s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00401 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s2)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00402 where

  proved : p (s3 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s3 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00403 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s3)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00404 where

  proved : p (s4 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00405 where

  proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00406 where

  proved : p (s5 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3 • s5)
  proved = checked (s5 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00407 where

  proved : p (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00408 where

  proved : p (s6 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00409 where

  proved : p (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00410 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00411 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s0)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00412 where

  proved : p (s1 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = checked (s1 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00413 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  proved = checked (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00414 where

  proved : p (s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00415 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s2)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00416 where

  proved : p (s3 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
  proved = checked (s3 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s6 • s5 • s4 • s5 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00417 where

  proved : p (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s3)
  proved = checked (s6 • s5 • s4 • s5 • s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00418 where

  proved : p (s4 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00419 where

  proved : p (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00420 where

  proved : p (s5 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
  proved = checked (s5 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00421 where

  proved : p (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s5)
  proved = checked (s5 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00422 where

  proved : p (s6 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
  proved = checked (s6 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00423 where

  proved : p (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s6)
  proved = checked (s6 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s6)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00424 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00425 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s0)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s0)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00426 where

  proved : p (s1 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
  proved = checked (s1 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00427 where

  proved : p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1)
  proved = checked (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00428 where

  proved : p (s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
  proved = checked (s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00429 where

  proved : p (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s2)
  proved = checked (s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s1 • s2)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00430 where

  proved : p (s3 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
  proved = checked (s3 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s5 • s4 • s5)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00431 where

  proved : p (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s3)
  proved = checked (s5 • s4 • s5 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s3)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00432 where

  proved : p (s4 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
  proved = checked (s4 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

module PE00433 where

  proved : p (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s4)
  proved = checked (s4 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1) (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s4)
    (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })
