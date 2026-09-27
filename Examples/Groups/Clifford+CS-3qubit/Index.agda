------------------------------------------------------------------------
-- Presentations of groups
--
-- This module provides data types for indices used in the naming of
-- generators.
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)

module Examples.Groups.Clifford+CS-3qubit.Index where

data Index : Set where
  ₀ : Index
  ₁ : Index
  ₂ : Index
  ₃ : Index
  ₄ : Index
  ₅ : Index
  ₆ : Index
  ₇ : Index

data Less : Index -> Index -> Set where
  ₀₁ : Less ₀ ₁
  ₀₂ : Less ₀ ₂
  ₀₃ : Less ₀ ₃
  ₀₄ : Less ₀ ₄
  ₀₅ : Less ₀ ₅
  ₀₆ : Less ₀ ₆
  ₀₇ : Less ₀ ₇
  ₁₂ : Less ₁ ₂
  ₁₃ : Less ₁ ₃
  ₁₄ : Less ₁ ₄
  ₁₅ : Less ₁ ₅
  ₁₆ : Less ₁ ₆
  ₁₇ : Less ₁ ₇
  ₂₃ : Less ₂ ₃
  ₂₄ : Less ₂ ₄
  ₂₅ : Less ₂ ₅
  ₂₆ : Less ₂ ₆
  ₂₇ : Less ₂ ₇
  ₃₄ : Less ₃ ₄
  ₃₅ : Less ₃ ₅
  ₃₆ : Less ₃ ₆
  ₃₇ : Less ₃ ₇
  ₄₅ : Less ₄ ₅
  ₄₆ : Less ₄ ₆
  ₄₇ : Less ₄ ₇
  ₅₆ : Less ₅ ₆
  ₅₇ : Less ₅ ₇
  ₆₇ : Less ₆ ₇


-- The not-equal relation on indices.
data Neq : Index -> Index -> Set where
  f<s : ∀ {i j} -> Less i j -> Neq i j
  f>s : ∀ {i j} -> Less j i -> Neq i j

pred : Index -> Index
pred ₀ = ₀
pred ₁ = ₀
pred ₂ = ₁
pred ₃ = ₂
pred ₄ = ₃
pred ₅ = ₄
pred ₆ = ₅
pred ₇ = ₆

transitivity : ∀ {j k l} -> (jk : Less j k) -> (kl : Less k l) -> Less j l
transitivity ₀₁ ₁₂ = ₀₂
transitivity ₀₁ ₁₃ = ₀₃
transitivity ₀₁ ₁₄ = ₀₄
transitivity ₀₁ ₁₅ = ₀₅
transitivity ₀₁ ₁₆ = ₀₆
transitivity ₀₁ ₁₇ = ₀₇
transitivity ₀₂ ₂₃ = ₀₃
transitivity ₀₂ ₂₄ = ₀₄
transitivity ₀₂ ₂₅ = ₀₅
transitivity ₀₂ ₂₆ = ₀₆
transitivity ₀₂ ₂₇ = ₀₇
transitivity ₀₃ ₃₄ = ₀₄
transitivity ₀₃ ₃₅ = ₀₅
transitivity ₀₃ ₃₆ = ₀₆
transitivity ₀₃ ₃₇ = ₀₇
transitivity ₀₄ ₄₅ = ₀₅
transitivity ₀₄ ₄₆ = ₀₆
transitivity ₀₄ ₄₇ = ₀₇
transitivity ₀₅ ₅₆ = ₀₆
transitivity ₀₅ ₅₇ = ₀₇
transitivity ₀₆ ₆₇ = ₀₇
transitivity ₀₇ ()
transitivity ₁₂ ₂₃ = ₁₃
transitivity ₁₂ ₂₄ = ₁₄
transitivity ₁₂ ₂₅ = ₁₅
transitivity ₁₂ ₂₆ = ₁₆
transitivity ₁₂ ₂₇ = ₁₇
transitivity ₁₃ ₃₄ = ₁₄
transitivity ₁₃ ₃₅ = ₁₅
transitivity ₁₃ ₃₆ = ₁₆
transitivity ₁₃ ₃₇ = ₁₇
transitivity ₁₄ ₄₅ = ₁₅
transitivity ₁₄ ₄₆ = ₁₆
transitivity ₁₄ ₄₇ = ₁₇
transitivity ₁₅ ₅₆ = ₁₆
transitivity ₁₅ ₅₇ = ₁₇
transitivity ₁₆ ₆₇ = ₁₇
transitivity ₁₇ ()
transitivity ₂₃ ₃₄ = ₂₄
transitivity ₂₃ ₃₅ = ₂₅
transitivity ₂₃ ₃₆ = ₂₆
transitivity ₂₃ ₃₇ = ₂₇
transitivity ₂₄ ₄₅ = ₂₅
transitivity ₂₄ ₄₆ = ₂₆
transitivity ₂₄ ₄₇ = ₂₇
transitivity ₂₅ ₅₆ = ₂₆
transitivity ₂₅ ₅₇ = ₂₇
transitivity ₂₆ ₆₇ = ₂₇
transitivity ₂₇ ()
transitivity ₃₄ ₄₅ = ₃₅
transitivity ₃₄ ₄₆ = ₃₆
transitivity ₃₄ ₄₇ = ₃₇
transitivity ₃₅ ₅₆ = ₃₆
transitivity ₃₅ ₅₇ = ₃₇
transitivity ₃₆ ₆₇ = ₃₇
transitivity ₃₇ ()
transitivity ₄₅ ₅₆ = ₄₆
transitivity ₄₅ ₅₇ = ₄₇
transitivity ₄₆ ₆₇ = ₄₇
transitivity ₄₇ ()
transitivity ₅₆ ₆₇ = ₅₇
transitivity ₅₇ ()
transitivity ₆₇ ()


anti-symmetry : ∀ {j k} -> Less j k -> Less k j -> ⊥
anti-symmetry ₀₁ ()
anti-symmetry ₀₂ ()
anti-symmetry ₀₃ ()
anti-symmetry ₀₄ ()
anti-symmetry ₀₅ ()
anti-symmetry ₀₆ ()
anti-symmetry ₀₇ ()
anti-symmetry ₁₂ ()
anti-symmetry ₁₃ ()
anti-symmetry ₁₄ ()
anti-symmetry ₁₅ ()
anti-symmetry ₁₆ ()
anti-symmetry ₁₇ ()
anti-symmetry ₂₃ ()
anti-symmetry ₂₄ ()
anti-symmetry ₂₅ ()
anti-symmetry ₂₆ ()
anti-symmetry ₂₇ ()
anti-symmetry ₃₄ ()
anti-symmetry ₃₅ ()
anti-symmetry ₃₆ ()
anti-symmetry ₃₇ ()
anti-symmetry ₄₅ ()
anti-symmetry ₄₆ ()
anti-symmetry ₄₇ ()
anti-symmetry ₅₆ ()
anti-symmetry ₅₇ ()
anti-symmetry ₆₇ ()

