------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the alternating group: the even permutations of Fin n.
--
-- A permutation is even when it is a product of an even number of
-- transpositions (Lafont, Section 2.4), i.e. when its sign (Parity) is
-- false.  Alt n pairs a permutation with that fact, and Alt-group n is
-- the group 𝔄ₙ they form under composition, compared as permutations:
-- a subgroup of Symmetric's Permutation′-group, closed under its
-- operations because the sign is a homomorphism.
--
-- Nothing here mentions the syntax.  cycle and shiftᴬ are named after
-- the generators they will interpret; the map from circuits to them is
-- Interpretation, and that it respects the relations is Soundness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Semantics where

open import Algebra.Bundles using (Group)
open import Algebra.Structures using (IsGroup)
open import Data.Bool using (false ; _xor_)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation
  using (Permutation′ ; permutation ; _∘ₚ_ ; id ; flip ; lift₀)
  renaming (_≈_ to _≈ₚ_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import ForStdlib.Data.Fin.Permutation.Properties using (∘ₚ-id-isGroup)
open import Level using (0ℓ)
open import Notations using (₀ ; ₁ ; ₂ ; ₁₊ ; ₃₊)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong₂)
open import Word.Base using (_•_)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Alternating.Parity

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Even permutations

record Alt (n : ℕ) : Set where
  field
    perm : Permutation′ n
    even : sign perm ≡ false

open Alt public

infix 4 _≈ᴬ_
_≈ᴬ_ : Rel (Alt n) 0ℓ
a ≈ᴬ b = perm a ≈ₚ perm b

------------------------------------------------------------------------
-- The group 𝔄ₙ

infixl 7 _∙ᴬ_
_∙ᴬ_ : Alt n → Alt n → Alt n
a ∙ᴬ b = record
  { perm = perm a ∘ₚ perm b
  ; even = trans (sign-∘ (perm a) (perm b)) (cong₂ _xor_ (even a) (even b))
  }

εᴬ : Alt n
εᴬ {n} = record { perm = id ; even = sign-id {n} }

infix 8 _⁻¹ᴬ
_⁻¹ᴬ : Alt n → Alt n
a ⁻¹ᴬ = record
  { perm = flip (perm a)
  ; even = trans (sign-flip (perm a)) (even a)
  }

-- Every law is the law of the permutations underneath.
Alt-isGroup : IsGroup (_≈ᴬ_ {n}) _∙ᴬ_ εᴬ _⁻¹ᴬ
Alt-isGroup {n} = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl  = λ _ → refl
          ; sym   = λ p i → sym (p i)
          ; trans = λ p q i → trans (p i) (q i)
          }
        ; ∙-cong = λ {a} {a′} {b} {b′} →
                     P.∙-cong {perm a} {perm a′} {perm b} {perm b′}
        }
      ; assoc = λ a b c → P.assoc (perm a) (perm b) (perm c)
      }
    ; identity = (λ a → P.identityˡ (perm a))
               , (λ a → P.identityʳ (perm a))
    }
  ; inverse = (λ a → P.inverseˡ (perm a)) , (λ a → P.inverseʳ (perm a))
  ; ⁻¹-cong = λ {a} {b} → P.⁻¹-cong {perm a} {perm b}
  }
  where module P = IsGroup (∘ₚ-id-isGroup n)

Alt-group : ℕ → Group 0ℓ 0ℓ
Alt-group n = record
  { Carrier = Alt n
  ; _≈_     = _≈ᴬ_
  ; _∙_     = _∙ᴬ_
  ; ε       = εᴬ
  ; _⁻¹     = _⁻¹ᴬ
  ; isGroup = Alt-isGroup
  }

------------------------------------------------------------------------
-- Semantic building blocks

private
  cycle-to : Fin (₃₊ n) → Fin (₃₊ n)
  cycle-to ₀      = ₁
  cycle-to ₁      = ₂
  cycle-to ₂      = ₀
  cycle-to (₃₊ k) = ₃₊ k

  cycle-from : Fin (₃₊ n) → Fin (₃₊ n)
  cycle-from ₀      = ₂
  cycle-from ₁      = ₀
  cycle-from ₂      = ₁
  cycle-from (₃₊ k) = ₃₊ k

-- The cyclic permutation of the wires 0 1 2, sending 0 to 1, 1 to 2
-- and 2 to 0: what ω will denote.
cycle : Permutation′ (₃₊ n)
cycle = permutation cycle-to cycle-from
  (λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; (₃₊ _) → refl })
  (λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; (₃₊ _) → refl })

-- It is two transpositions: the swap of the wires 1 2, then that of
-- the wires 0 1 (the picture defining ω on p. 267).
cycle-even : sign (cycle {n}) ≡ false
cycle-even {n} = sign-of {₃₊ n} (S.σ S.↑ • S.σ) cycle
  λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; (₃₊ _) → refl }

cycleᴬ : Alt (₃₊ n)
cycleᴬ {n} = record { perm = cycle ; even = cycle-even {n} }

-- Shift a permutation up by one wire: what _↥ will act as.
shiftᴬ : Alt n → Alt (₁₊ n)
shiftᴬ a = record
  { perm = lift₀ (perm a)
  ; even = trans (sign-lift₀ (perm a)) (even a)
  }
