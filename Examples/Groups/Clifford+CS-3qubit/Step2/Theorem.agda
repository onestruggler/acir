------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≟_ ; _≤?_)
open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)

module Examples.Groups.Clifford+CS-3qubit.Step2.Theorem where

module TwoLevel-Simplified where
  -- The new set of generators.
  data Gen : Set where
    i₀-gen : Gen
    K₀₁-gen : Gen
    X₀₁-gen : Gen
    X₁₂-gen : Gen
    X₂₃-gen : Gen
    X₃₄-gen : Gen
    X₄₅-gen : Gen
    X₅₆-gen : Gen
    X₆₇-gen : Gen

  instance
    MaybeEq-Gen : MaybeEq Gen
    MaybeEq-Gen = record { _=m?_ = λ{
      i₀-gen i₀-gen → just Eq.refl ;
      K₀₁-gen K₀₁-gen → just Eq.refl ;
      X₀₁-gen X₀₁-gen → just Eq.refl ;
      X₁₂-gen X₁₂-gen → just Eq.refl ;
      X₂₃-gen X₂₃-gen → just Eq.refl ;
      X₃₄-gen X₃₄-gen → just Eq.refl ;
      X₄₅-gen X₄₅-gen → just Eq.refl ;
      X₅₆-gen X₅₆-gen → just Eq.refl ;
      X₆₇-gen X₆₇-gen → just Eq.refl ;
      x y -> nothing } }
  

  -- For convenience, we define a singleton word for each new
  -- generator, as well as for all of the original 2-level generators.
  -- This makes the relations easier to state.

  mX-aux : Index -> Index -> Word Gen
  mX-aux ₀ ₁ = [ X₀₁-gen ]ʷ
  mX-aux ₁ ₂ = [ X₁₂-gen ]ʷ
  mX-aux ₂ ₃ = [ X₂₃-gen ]ʷ
  mX-aux ₃ ₄ = [ X₃₄-gen ]ʷ
  mX-aux ₄ ₅ = [ X₄₅-gen ]ʷ
  mX-aux ₅ ₆ = [ X₅₆-gen ]ʷ
  mX-aux ₆ ₇ = [ X₆₇-gen ]ʷ
  mX-aux _ _ = ε

  mX' : ℕ -> Index -> Index -> Word Gen
  mX' 0 _ _ = ε
  mX' (suc n) l m with l =m? pred m
  ... | nothing = mX-aux (pred m) m • mX' n l (pred m) • mX-aux (pred m) m
  ... | just _ = mX-aux l m

  mX = mX' 100


  X₀₁ : Word Gen
  X₀₁ = [ X₀₁-gen ]ʷ

  X₁₂ : Word Gen
  X₁₂ = [ X₁₂-gen ]ʷ

  X₂₃ : Word Gen
  X₂₃ = [ X₂₃-gen ]ʷ

  X₃₄ : Word Gen
  X₃₄ = [ X₃₄-gen ]ʷ

  X₄₅ : Word Gen
  X₄₅ = [ X₄₅-gen ]ʷ

  X₅₆ : Word Gen
  X₅₆ = [ X₅₆-gen ]ʷ

  X₆₇ : Word Gen
  X₆₇ = [ X₆₇-gen ]ʷ

  X₀₂ : Word Gen
  X₀₂ = X₁₂ • X₀₁ • X₁₂

  X₀₃ : Word Gen
  X₀₃ = X₂₃ • X₀₂ • X₂₃

  X₀₄ : Word Gen
  X₀₄ = X₃₄ • X₀₃ • X₃₄

  X₀₅ : Word Gen
  X₀₅ = X₄₅ • X₀₄ • X₄₅

  X₀₆ : Word Gen
  X₀₆ = X₅₆ • X₀₅ • X₅₆

  X₀₇ : Word Gen
  X₀₇ = X₆₇ • X₀₆ • X₆₇

  X₁₃ : Word Gen
  X₁₃ = X₂₃ • X₁₂ • X₂₃

  X₁₄ : Word Gen
  X₁₄ = X₃₄ • X₁₃ • X₃₄

  X₁₅ : Word Gen
  X₁₅ = X₄₅ • X₁₄ • X₄₅

  X₁₆ : Word Gen
  X₁₆ = X₅₆ • X₁₅ • X₅₆

  X₁₇ : Word Gen
  X₁₇ = X₆₇ • X₁₆ • X₆₇

  X₂₄ : Word Gen
  X₂₄ = X₃₄ • X₂₃ • X₃₄

  X₂₅ : Word Gen
  X₂₅ = X₄₅ • X₂₄ • X₄₅

  X₂₆ : Word Gen
  X₂₆ = X₅₆ • X₂₅ • X₅₆

  X₂₇ : Word Gen
  X₂₇ = X₆₇ • X₂₆ • X₆₇

  X₃₅ : Word Gen
  X₃₅ = X₄₅ • X₃₄ • X₄₅

  X₃₆ : Word Gen
  X₃₆ = X₅₆ • X₃₅ • X₅₆

  X₃₇ : Word Gen
  X₃₇ = X₆₇ • X₃₆ • X₆₇

  X₄₆ : Word Gen
  X₄₆ = X₅₆ • X₄₅ • X₅₆

  X₄₇ : Word Gen
  X₄₇ = X₆₇ • X₄₆ • X₆₇

  X₅₇ : Word Gen
  X₅₇ = X₆₇ • X₅₆ • X₆₇

  mK' : ℕ -> Index -> Index -> Word Gen
  mK' 0 _ _ = ε
  mK' (suc l) ₀ ₁ = [ K₀₁-gen ]ʷ
  mK' (suc l) ₀ n = mX (pred n) n • mK' l ₀ (pred n) • mX (pred n) n
  mK' (suc l) m n = mX (pred m) m • mK' l (pred m) n • mX (pred m) m

  mK = mK' 200


  i₀ : Word Gen
  i₀ = [ i₀-gen ]ʷ

  i₁ : Word Gen
  i₁ = X₀₁ • i₀ • X₀₁

  i₂ : Word Gen
  i₂ = X₁₂ • i₁ • X₁₂

  i₃ : Word Gen
  i₃ = X₂₃ • i₂ • X₂₃

  i₄ : Word Gen
  i₄ = X₃₄ • i₃ • X₃₄

  i₅ : Word Gen
  i₅ = X₄₅ • i₄ • X₄₅

  i₆ : Word Gen
  i₆ = X₅₆ • i₅ • X₅₆

  i₇ : Word Gen
  i₇ = X₆₇ • i₆ • X₆₇

  K₀₁ : Word Gen
  K₀₁ = [ K₀₁-gen ]ʷ

  K₁₂ : Word Gen
  K₁₂ = mK ₁ ₂

  K₂₃ : Word Gen
  K₂₃ = mK ₂ ₃

  K₃₄ : Word Gen
  K₃₄ = mK ₃ ₄

  K₄₅ : Word Gen
  K₄₅ = mK ₄ ₅

  K₅₆ : Word Gen
  K₅₆ = mK ₅ ₆

  K₆₇ : Word Gen
  K₆₇ = mK ₆ ₇

  K₀₂ : Word Gen
  K₀₂ = X₁₂ • K₀₁ • X₁₂

  K₀₃ : Word Gen
  K₀₃ = X₂₃ • K₀₂ • X₂₃

  K₀₄ : Word Gen
  K₀₄ = X₃₄ • K₀₃ • X₃₄

  K₀₅ : Word Gen
  K₀₅ = X₄₅ • K₀₄ • X₄₅

  K₀₆ : Word Gen
  K₀₆ = X₅₆ • K₀₅ • X₅₆

  K₀₇ : Word Gen
  K₀₇ = X₆₇ • K₀₆ • X₆₇

  K₁₃ : Word Gen
  K₁₃ = X₂₃ • K₁₂ • X₂₃

  K₁₄ : Word Gen
  K₁₄ = X₃₄ • K₁₃ • X₃₄

  K₁₅ : Word Gen
  K₁₅ = X₄₅ • K₁₄ • X₄₅

  K₁₆ : Word Gen
  K₁₆ = X₅₆ • K₁₅ • X₅₆

  K₁₇ : Word Gen
  K₁₇ = X₆₇ • K₁₆ • X₆₇

  K₂₄ : Word Gen
  K₂₄ = X₃₄ • K₂₃ • X₃₄

  K₂₅ : Word Gen
  K₂₅ = X₄₅ • K₂₄ • X₄₅

  K₂₆ : Word Gen
  K₂₆ = X₅₆ • K₂₅ • X₅₆

  K₂₇ : Word Gen
  K₂₇ = X₆₇ • K₂₆ • X₆₇

  K₃₅ : Word Gen
  K₃₅ = X₄₅ • K₃₄ • X₄₅

  K₃₆ : Word Gen
  K₃₆ = X₅₆ • K₃₅ • X₅₆

  K₃₇ : Word Gen
  K₃₇ = X₆₇ • K₃₆ • X₆₇

  K₄₆ : Word Gen
  K₄₆ = X₅₆ • K₄₅ • X₅₆

  K₄₇ : Word Gen
  K₄₇ = X₆₇ • K₄₆ • X₆₇

  K₅₇ : Word Gen
  K₅₇ = X₆₇ • K₅₆ • X₆₇


  -- The new set of relations.
  data Rel : Context Gen where
    [S1] : i₀ ^ 4 === ε ∈ Rel

    [S3a] : X₀₁ ^ 2 === ε ∈ Rel
    [S3b] : X₁₂ ^ 2 === ε ∈ Rel
    [S3c] : X₂₃ ^ 2 === ε ∈ Rel
    [S3d] : X₃₄ ^ 2 === ε ∈ Rel
    [S3e] : X₄₅ ^ 2 === ε ∈ Rel
    [S3f] : X₅₆ ^ 2 === ε ∈ Rel
    [S3g] : X₆₇ ^ 2 === ε ∈ Rel

    [S4a] : i₁ • i₀ === i₀ • i₁ ∈ Rel
    [S4b] : i₂ • K₀₁ === K₀₁ • i₂ ∈ Rel

    [S5a] : i₀ • X₁₂ === X₁₂ • i₀ ∈ Rel
    [S5b] : i₀ • X₂₃ === X₂₃ • i₀ ∈ Rel
    [S5c] : i₀ • X₃₄ === X₃₄ • i₀ ∈ Rel
    [S5d] : i₀ • X₄₅ === X₄₅ • i₀ ∈ Rel
    [S5e] : i₀ • X₅₆ === X₅₆ • i₀ ∈ Rel
    [S5f] : i₀ • X₆₇ === X₆₇ • i₀ ∈ Rel

    [S6] : K₂₃ • K₀₁ === K₀₁ • K₂₃ ∈ Rel

    [S7a] : K₀₁ • X₂₃ === X₂₃ • K₀₁ ∈ Rel
    [S7b] : K₀₁ • X₃₄ === X₃₄ • K₀₁ ∈ Rel
    [S7c] : K₀₁ • X₄₅ === X₄₅ • K₀₁ ∈ Rel
    [S7d] : K₀₁ • X₅₆ === X₅₆ • K₀₁ ∈ Rel
    [S7e] : K₀₁ • X₆₇ === X₆₇ • K₀₁ ∈ Rel

    [S8a] : X₂₃ • X₀₁ === X₀₁ • X₂₃ ∈ Rel
    [S8b] : X₃₄ • X₀₁ === X₀₁ • X₃₄ ∈ Rel
    [S8c] : X₄₅ • X₀₁ === X₀₁ • X₄₅ ∈ Rel
    [S8d] : X₅₆ • X₀₁ === X₀₁ • X₅₆ ∈ Rel
    [S8e] : X₆₇ • X₀₁ === X₀₁ • X₆₇ ∈ Rel
    [S8f] : X₃₄ • X₁₂ === X₁₂ • X₃₄ ∈ Rel
    [S8g] : X₄₅ • X₁₂ === X₁₂ • X₄₅ ∈ Rel
    [S8h] : X₅₆ • X₁₂ === X₁₂ • X₅₆ ∈ Rel
    [S8i] : X₆₇ • X₁₂ === X₁₂ • X₆₇ ∈ Rel
    [S8j] : X₄₅ • X₂₃ === X₂₃ • X₄₅ ∈ Rel
    [S8k] : X₅₆ • X₂₃ === X₂₃ • X₅₆ ∈ Rel
    [S8l] : X₆₇ • X₂₃ === X₂₃ • X₆₇ ∈ Rel
    [S8m] : X₅₆ • X₃₄ === X₃₄ • X₅₆ ∈ Rel
    [S8n] : X₆₇ • X₃₄ === X₃₄ • X₆₇ ∈ Rel
    [S8o] : X₆₇ • X₄₅ === X₄₅ • X₆₇ ∈ Rel

    [S9a] : X₁₂ • X₀₁ • X₁₂ === X₀₁ • X₁₂ • X₀₁ ∈ Rel
    [S9b] : X₂₃ • X₁₂ • X₂₃ === X₁₂ • X₂₃ • X₁₂ ∈ Rel
    [S9c] : X₃₄ • X₂₃ • X₃₄ === X₂₃ • X₃₄ • X₂₃ ∈ Rel
    [S9d] : X₄₅ • X₃₄ • X₄₅ === X₃₄ • X₄₅ • X₃₄ ∈ Rel
    [S9e] : X₅₆ • X₄₅ • X₅₆ === X₄₅ • X₅₆ • X₄₅ ∈ Rel
    [S9f] : X₆₇ • X₅₆ • X₆₇ === X₅₆ • X₆₇ • X₅₆ ∈ Rel

    [S10] : K₀₁ • i₁ ^ 2 === X₀₁ • K₀₁ ∈ Rel
    [S11] : i₁ • K₀₁ • i₁ • K₀₁ === K₀₁ • i₁ ^ 3 ∈ Rel
    [S12] : K₀₁ • i₀ • i₁ === i₀ • i₁ • K₀₁ ∈ Rel
    [S14] : K₀₁ ^ 2 • i₀ • i₁ === ε ∈ Rel
    [S15] : K₀₂ • K₁₃ • K₀₁ • K₂₃ === K₀₁ • K₂₃ • K₀₂ • K₁₃ ∈ Rel


open TwoLevel-Simplified
open TwoLevel-Less

-- Translation from the new to the old generators.
f : TwoLevel-Simplified.Gen -> Word TwoLevel-Less.Gen
f i₀-gen = i ₀
f K₀₁-gen = K ₀₁
f X₀₁-gen = X ₀₁
f X₁₂-gen = X ₁₂
f X₂₃-gen = X ₂₃
f X₃₄-gen = X ₃₄
f X₄₅-gen = X ₄₅
f X₅₆-gen = X ₅₆
f X₆₇-gen = X ₆₇

-- ----------------------------------------------------------------------
-- * Statement of completeness and soundness of the new relations

soundness-property : Set
soundness-property = TwoLevel-Simplified.Rel is-sound-wrt TwoLevel-Less.Rel and f

completeness-property : Set
completeness-property = TwoLevel-Simplified.Rel is-complete-wrt TwoLevel-Less.Rel and f


-- We put the reverse translation here for convenience. The properties
-- stated do not depend on it.

-- Translation from the old to the new generators.
g : TwoLevel-Less.Gen -> Word TwoLevel-Simplified.Gen
g (i-gen ₀) = i₀
g (i-gen ₁) = i₁
g (i-gen ₂) = i₂
g (i-gen ₃) = i₃
g (i-gen ₄) = i₄
g (i-gen ₅) = i₅
g (i-gen ₆) = i₆
g (i-gen ₇) = i₇

g (X-gen {₀} {₁} jk) = X₀₁
g (X-gen {₀} {₂} jk) = X₀₂
g (X-gen {₀} {₃} jk) = X₀₃
g (X-gen {₀} {₄} jk) = X₀₄
g (X-gen {₀} {₅} jk) = X₀₅
g (X-gen {₀} {₆} jk) = X₀₆
g (X-gen {₀} {₇} jk) = X₀₇

g (X-gen {₁} {₂} jk) = X₁₂
g (X-gen {₁} {₃} jk) = X₁₃
g (X-gen {₁} {₄} jk) = X₁₄
g (X-gen {₁} {₅} jk) = X₁₅
g (X-gen {₁} {₆} jk) = X₁₆
g (X-gen {₁} {₇} jk) = X₁₇

g (X-gen {₂} {₃} jk) = X₂₃
g (X-gen {₂} {₄} jk) = X₂₄
g (X-gen {₂} {₅} jk) = X₂₅
g (X-gen {₂} {₆} jk) = X₂₆
g (X-gen {₂} {₇} jk) = X₂₇

g (X-gen {₃} {₄} jk) = X₃₄
g (X-gen {₃} {₅} jk) = X₃₅
g (X-gen {₃} {₆} jk) = X₃₆
g (X-gen {₃} {₇} jk) = X₃₇

g (X-gen {₄} {₅} jk) = X₄₅
g (X-gen {₄} {₆} jk) = X₄₆
g (X-gen {₄} {₇} jk) = X₄₇

g (X-gen {₅} {₆} jk) = X₅₆
g (X-gen {₅} {₇} jk) = X₅₇
g (X-gen {₅} {₅} ())
g (X-gen {₆} {₅} ())

g (X-gen {₆} {₆} ())
g (X-gen {₇} {₆} ())
g (X-gen {₆} {₇} _) = X₆₇
g (X-gen {₇} {₇} ())


g (K-gen {₀} {₁} jk) = K₀₁
g (K-gen {₀} {₂} jk) = K₀₂
g (K-gen {₀} {₃} jk) = K₀₃
g (K-gen {₀} {₄} jk) = K₀₄
g (K-gen {₀} {₅} jk) = K₀₅
g (K-gen {₀} {₆} jk) = K₀₆
g (K-gen {₀} {₇} jk) = K₀₇

g (K-gen {₁} {₂} jk) = K₁₂
g (K-gen {₁} {₃} jk) = K₁₃
g (K-gen {₁} {₄} jk) = K₁₄
g (K-gen {₁} {₅} jk) = K₁₅
g (K-gen {₁} {₆} jk) = K₁₆
g (K-gen {₁} {₇} jk) = K₁₇

g (K-gen {₂} {₃} jk) = K₂₃
g (K-gen {₂} {₄} jk) = K₂₄
g (K-gen {₂} {₅} jk) = K₂₅
g (K-gen {₂} {₆} jk) = K₂₆
g (K-gen {₂} {₇} jk) = K₂₇

g (K-gen {₃} {₄} jk) = K₃₄
g (K-gen {₃} {₅} jk) = K₃₅
g (K-gen {₃} {₆} jk) = K₃₆
g (K-gen {₃} {₇} jk) = K₃₇

g (K-gen {₄} {₅} jk) = K₄₅
g (K-gen {₄} {₆} jk) = K₄₆
g (K-gen {₄} {₇} jk) = K₄₇

g (K-gen {₅} {₆} jk) = K₅₆
g (K-gen {₅} {₇} jk) = K₅₇
g (K-gen {₅} {₅} ())
g (K-gen {₆} {₅} ())
g (K-gen {₆} {₆} ())
g (K-gen {₇} {₆} ())
g (K-gen {₆} {₇} jk) = K₆₇
g (K-gen {₇} {₇} ())

