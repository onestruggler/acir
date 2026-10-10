------------------------------------------------------------------------
-- Presentations of groups
--
-- The generators and relations of §5 of Li, Ross and Selinger: the set
-- ℱₙ (Definition 5.2) adds to 𝒢ₙ the global generator
--
--   I ⊗ H = diag(H, …, H),
--
-- and the relations are those of Table 1, on the generators of 𝒢ₙ,
-- and of Table 2 (Definition 5.3).  Indices start at 0, so the blocks
-- of I ⊗ H are {0, 1}, {2, 3}, ….
--
-- As printed, (7d) has its exponents exchanged: for a odd (the paper's
-- indices, from 1) the block {a, a+1} is one of I ⊗ H, H X H = Z there,
-- and (I⊗H) X_[a,a+1] (I⊗H) is (-1)_[a+1]; for a even it is
-- X_[a,a+1] K_[a-1,a,a+1,a+2].  The printed right side
-- (-1)_[a+1]^(a+1) X_[a,a+1]^a K_[a-1,a,a+1,a+2]^a has the cases the
-- other way round.  Here they are r7d₀ (x even, from 0) and r7d₁
-- (x odd).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics where

open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
open import Data.Nat.Base using (ℕ ; suc ; _%_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as S using (Gen ; M-gen ; X-gen ; K-gen)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Generators

infix 10 ⌊_⌋

data Genᴸ (n : ℕ) : Set where
  ⌊_⌋ : Gen n → Genᴸ n
  IH  : Genᴸ n

-- The words over 𝒢ₙ among those over ℱₙ.
⌊_⌋ʷ : Word (Gen n) → Word (Genᴸ n)
⌊_⌋ʷ = wmap ⌊_⌋

-- I ⊗ H, (-1)_[a], X_[a,b] and K_[a,b,c,d] as words.
H : Word (Genᴸ n)
H = [ IH ]ʷ

Mᴸ : Fin n → Word (Genᴸ n)
Mᴸ a = [ ⌊ M-gen a ⌋ ]ʷ

Xᴸ : (a b : Fin n) → .(a < b) → Word (Genᴸ n)
Xᴸ a b p = [ ⌊ X-gen a b p ⌋ ]ʷ

Kᴸ : (a b c d : Fin n) → .(a < b) → .(b < c) → .(c < d) → Word (Genᴸ n)
Kᴸ a b c d p q r = [ ⌊ K-gen a b c d p q r ⌋ ]ʷ

------------------------------------------------------------------------
-- The relations of Tables 1 and 2

infix 4 _===ᴸ_

data _===ᴸ_ {n : ℕ} : WRel (Genᴸ n) where
  -- Table 1, on the generators of 𝒢ₙ.
  table1 : ∀ {w v} → w S.=== v → ⌊ w ⌋ʷ ===ᴸ ⌊ v ⌋ʷ

  -- (7a)
  r7a : H • H ===ᴸ ε

  -- (7b)
  r7b : ∀ {a b c d : Fin n} .(p : a < b) .(q : b < c) .(r : c < d) →
        toℕ a ≡ 0 → toℕ b ≡ 1 → toℕ c ≡ 2 → toℕ d ≡ 3 →
        H • Kᴸ a b c d p q r • H ===ᴸ Kᴸ a b c d p q r

  -- (7c)
  r7c : ∀ {a b : Fin n} .(p : a < b) → toℕ a ≡ 0 → toℕ b ≡ 1 →
        H • Mᴸ a • H ===ᴸ Mᴸ a • Xᴸ a b p • Mᴸ a

  -- (7d), x even: {x, x+1} is a block, and H X H = Z.
  r7d₀ : ∀ {x y : Fin n} .(p : x < y) → toℕ y ≡ suc (toℕ x) → toℕ x % 2 ≡ 0 →
         H • Xᴸ x y p • H ===ᴸ Mᴸ y

  -- (7d), x odd.
  r7d₁ : ∀ {w x y z : Fin n} .(p : w < x) .(q : x < y) .(r : y < z) →
         toℕ x ≡ suc (toℕ w) → toℕ y ≡ suc (toℕ x) → toℕ z ≡ suc (toℕ y) → toℕ x % 2 ≡ 1 →
         H • Xᴸ x y q • H ===ᴸ Xᴸ x y q • Kᴸ w x y z p q r

------------------------------------------------------------------------
-- Derivations over 𝒢ₙ are derivations over ℱₙ

⌊⌋-cong : ∀ {w v : Word (Gen n)} → PB._≈_ (S._===_ {n}) w v → PB._≈_ (_===ᴸ_ {n}) ⌊ w ⌋ʷ ⌊ v ⌋ʷ
⌊⌋-cong {n} = PP.GenCongruence.fʷ-cong (S._===_ {n}) (_===ᴸ_ {n}) ⌊_⌋ (λ h → PB.axiom (table1 h))
