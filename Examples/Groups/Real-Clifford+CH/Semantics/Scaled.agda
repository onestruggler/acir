------------------------------------------------------------------------
-- Presentations of groups
--
-- Operators over ℤ[1/√2], as operators over ℤ[√2] with a power of 1/√2
--
-- A circuit of ℓ gates denotes (1/√2)^ℓ · M for a matrix M over ℤ[√2]
-- (Semantics.Ring).  Rather than divide, the semantics carries the
-- pair (ℓ , M), and identifies two pairs when they denote the same
-- matrix over ℤ[1/√2]:
--
--     (ℓ , M) ~ (ℓ' , M')   iff   √2^ℓ' · M ≐ √2^ℓ · M'.
--
-- This is the localisation of ℤ[√2] at √2, done on matrices; it is an
-- equivalence because √2 is not a zero divisor (Ring.√2^-cancel), and
-- a congruence for the product (ℓ , M) ∙ (ℓ' , M') = (ℓ + ℓ' , M ⊙ M')
-- because scalars pass through products.  The monoid Scaled-monoid n is
-- the semantic domain of Clément's Definition 2.3: the 2ⁿ × 2ⁿ matrices
-- over ℤ[1/√2], with equality of matrices.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Semantics.Scaled where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Data.Nat.Properties as NP

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Scalar multiples of operators and matrices

infixr 7 _·_

_·_ : 𝔽 → Op n → Op n
(c · M) x y = c * M x y

scaleM : 𝔽 → Mat k → Mat k
scaleM c M = matOf (c · ix M)

ix-scaleM : (c : 𝔽) (M : Mat k) → ix (scaleM c M) ≐ (c · ix M)
ix-scaleM c M = ix-matOf (c · ix M)

·-cong : {c d : 𝔽} {M N : Op n} → c ≡ d → M ≐ N → (c · M) ≐ (d · N)
·-cong e f x y = Eq.cong₂ _*_ e (f x y)

·-1 : (M : Op n) → (1# · M) ≐ M
·-1 M x y = *-identityˡ (M x y)

·-assoc : (c d : 𝔽) (M : Op n) → (c · (d · M)) ≐ ((c * d) · M)
·-assoc c d M x y = Eq.sym (*-assoc c d (M x y))

·-comm : (c d : 𝔽) (M : Op n) → (c · (d · M)) ≐ (d · (c · M))
·-comm c d M x y = Eq.trans (Eq.sym (*-assoc c d (M x y)))
  (Eq.trans (Eq.cong (_* M x y) (*-comm c d)) (*-assoc d c (M x y)))

-- Scalars pass through products.
·-⊙ : (c d : 𝔽) (M N : Op n) → ((c · M) ⊙ (d · N)) ≐ ((c * d) · (M ⊙ N))
·-⊙ c d M N x y =
  Eq.trans (Σ-cong {f = λ z → (c * M x z) * (d * N z y)}
                    {g = λ z → (c * d) * (M x z * N z y)}
                    (λ z → *-cross c (M x z) d (N z y)))
           (Σ-scaleˡ (c * d) (λ z → M x z * N z y))

------------------------------------------------------------------------
-- The scaled operators and their equivalence

Scaled : ℕ → Set
Scaled n = ℕ × Op n

infix 4 _~_

_~_ : Scaled n → Scaled n → Set
s ~ t = ((√2^ proj₁ t) · proj₂ s) ≐ ((√2^ proj₁ s) · proj₂ t)

~-reflexive : {l l' : ℕ} {M M' : Op n} → l ≡ l' → M ≐ M' → (l , M) ~ (l' , M')
~-reflexive {l = l} Eq.refl e = ·-cong Eq.refl e

~-refl : (s : Scaled n) → s ~ s
~-refl (l , M) = ·-cong Eq.refl (≐-refl M)

~-sym : {s t : Scaled n} → s ~ t → t ~ s
~-sym e = ≐-sym e

~-trans : {s t u : Scaled n} → s ~ t → t ~ u → s ~ u
~-trans {s = l₁ , M₁} {l₂ , M₂} {l₃ , M₃} e f x y =
  √2^-cancel l₂ (√2^ l₃ * M₁ x y) (√2^ l₁ * M₃ x y) (begin
    √2^ l₂ * (√2^ l₃ * M₁ x y)   ≡⟨ swap (√2^ l₂) (√2^ l₃) (M₁ x y) ⟩
    √2^ l₃ * (√2^ l₂ * M₁ x y)   ≡⟨ Eq.cong (√2^ l₃ *_) (e x y) ⟩
    √2^ l₃ * (√2^ l₁ * M₂ x y)   ≡⟨ swap (√2^ l₃) (√2^ l₁) (M₂ x y) ⟩
    √2^ l₁ * (√2^ l₃ * M₂ x y)   ≡⟨ Eq.cong (√2^ l₁ *_) (f x y) ⟩
    √2^ l₁ * (√2^ l₂ * M₃ x y)   ≡⟨ swap (√2^ l₁) (√2^ l₂) (M₃ x y) ⟩
    √2^ l₂ * (√2^ l₁ * M₃ x y)   ∎)
  where
  open Eq.≡-Reasoning
  swap : ∀ p q a → p * (q * a) ≡ q * (p * a)
  swap p q a = Eq.trans (Eq.sym (*-assoc p q a))
    (Eq.trans (Eq.cong (_* a) (*-comm p q)) (*-assoc q p a))

------------------------------------------------------------------------
-- The monoid

infixl 7 _∙_

_∙_ : Scaled n → Scaled n → Scaled n
s ∙ t = (proj₁ s +ℕ proj₁ t , proj₂ s ⊙ proj₂ t)

ε∙ : Scaled n
ε∙ = (0 , Idₒ)

∙-cong : {s s' t t' : Scaled n} → s ~ s' → t ~ t' → (s ∙ t) ~ (s' ∙ t')
∙-cong {s = l₁ , M₁} {l₁' , M₁'} {l₂ , M₂} {l₂' , M₂'} e f =
  ≐-trans (·-cong (√2^-+ l₁' l₂') (≐-refl (M₁ ⊙ M₂)))
    (≐-trans (≐-sym (·-⊙ (√2^ l₁') (√2^ l₂') M₁ M₂))
      (≐-trans (⊙-cong e f)
        (≐-trans (·-⊙ (√2^ l₁) (√2^ l₂) M₁' M₂')
                 (·-cong (Eq.sym (√2^-+ l₁ l₂)) (≐-refl (M₁' ⊙ M₂'))))))

∙-assoc : (s t u : Scaled n) → ((s ∙ t) ∙ u) ~ (s ∙ (t ∙ u))
∙-assoc (l₁ , M₁) (l₂ , M₂) (l₃ , M₃) =
  ~-reflexive (NP.+-assoc l₁ l₂ l₃) (⊙-assoc M₁ M₂ M₃)

∙-identityˡ : (s : Scaled n) → (ε∙ ∙ s) ~ s
∙-identityˡ (l , M) = ~-reflexive {l = l} {l} Eq.refl (⊙-identityˡ M)

∙-identityʳ : (s : Scaled n) → (s ∙ ε∙) ~ s
∙-identityʳ (l , M) = ~-reflexive (NP.+-identityʳ l) (⊙-identityʳ M)

-- The 2ⁿ × 2ⁿ matrices over ℤ[1/√2] under multiplication.
Scaled-monoid : ℕ → Monoid 0ℓ 0ℓ
Scaled-monoid n = record
  { Carrier  = Scaled n
  ; _≈_      = _~_
  ; _∙_      = _∙_
  ; ε        = ε∙
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl  = λ {s} → ~-refl s
          ; sym   = λ {s} {t} → ~-sym {s = s} {t}
          ; trans = λ {s} {t} {u} → ~-trans {s = s} {t} {u}
          }
        ; ∙-cong = λ {s} {s'} {t} {t'} → ∙-cong {s = s} {s'} {t} {t'}
        }
      ; assoc = ∙-assoc
      }
    ; identity = ∙-identityˡ , ∙-identityʳ
    }
  }

------------------------------------------------------------------------
-- Scalars through one factor, and stored matrices under ≡

·-⊙ˡ : (c : 𝔽) (M N : Op n) → ((c · M) ⊙ N) ≐ (c · (M ⊙ N))
·-⊙ˡ c M N x y =
  Eq.trans (Σ-cong {f = λ z → (c * M x z) * N z y}
                    {g = λ z → c * (M x z * N z y)}
                    (λ z → *-assoc c (M x z) (N z y)))
           (Σ-scaleˡ c (λ z → M x z * N z y))

·-⊙ʳ : (c : 𝔽) (M N : Op n) → (M ⊙ (c · N)) ≐ (c · (M ⊙ N))
·-⊙ʳ c M N x y =
  Eq.trans (Σ-cong {f = λ z → M x z * (c * N z y)}
                    {g = λ z → c * (M x z * N z y)}
                    (λ z → Eq.trans (Eq.sym (*-assoc (M x z) c (N z y)))
                            (Eq.trans (Eq.cong (_* N z y) (*-comm (M x z) c))
                                      (*-assoc c (M x z) (N z y)))))
           (Σ-scaleˡ c (λ z → M x z * N z y))

ix-≡ : {M N : Mat k} → M ≡ N → ix M ≐ ix N
ix-≡ {M = M} Eq.refl = ≐-refl (ix M)
