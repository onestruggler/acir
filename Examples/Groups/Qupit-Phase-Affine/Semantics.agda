------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of phase-affine circuits (Section 3.3)
--
-- A phase-affine operator P_g D_q sends a basis state to a basis state
-- up to a power of ω = e^{2πi/p}:
--
--     P_g D_q |x⟩ = ω^(q x) |g x⟩,
--
-- so it is the pair of a function g on labels x ∈ F_pⁿ and a phase
-- q with values in F_p, kept as the function x ↦ (g x , q x).
-- Composition composes the label functions and adds the phases along
-- the way (Definition 12: P_{g₂}D_{q₂} ∘ P_{g₁}D_{q₁} = P_{g₂g₁} D_{q₁ +
-- q₂∘g₁}).  Operators are compared pointwise (_≐_).
--
-- Composition is in operator order, as for matrices: in M ⊙ N, N acts
-- first, and the map to matrices (Matrix) is a homomorphism.
--
-- Wire 0 is the bottom wire and comes first in a label vector.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Semantics (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Algebra.Bundles using (Monoid)
open import Data.Nat.Base as ℕ using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Field p-2 p-prime public

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Operators

Labels : ℕ → Set
Labels n = Vec F n

-- x ↦ (g x , q x).
Op : ℕ → Set
Op n = Labels n → Labels n × F

Idₒ : Op n
Idₒ x = x , 0F

-- Composition in operator order: N first, then M.
infixr 7 _⊙_

_⊙_ : Op n → Op n → Op n
(M ⊙ N) x = proj₁ (M (proj₁ (N x))) , proj₂ (N x) + proj₂ (M (proj₁ (N x)))

-- Pointwise equality.
infix 4 _≐_

_≐_ : Op n → Op n → Set
M ≐ N = ∀ x → M x ≡ N x

≐-refl : (M : Op n) → M ≐ M
≐-refl M x = refl

≐-sym : {M N : Op n} → M ≐ N → N ≐ M
≐-sym e x = sym (e x)

≐-trans : {M N P : Op n} → M ≐ N → N ≐ P → M ≐ P
≐-trans e f x = trans (e x) (f x)

⊙-cong : {M M' N N' : Op n} → M ≐ M' → N ≐ N' → (M ⊙ N) ≐ (M' ⊙ N')
⊙-cong {M = M} {M'} {N} {N'} e f x
  rewrite f x | e (proj₁ (N' x)) = refl

⊙-assoc : (M N P : Op n) → ((M ⊙ N) ⊙ P) ≐ (M ⊙ (N ⊙ P))
⊙-assoc M N P x = cong (proj₁ (M (proj₁ (N (proj₁ (P x))))) ,_)
  (sym (FR.+-assoc (proj₂ (P x)) (proj₂ (N (proj₁ (P x)))) (proj₂ (M (proj₁ (N (proj₁ (P x))))))))

⊙-identityˡ : (M : Op n) → (Idₒ ⊙ M) ≐ M
⊙-identityˡ M x = cong (proj₁ (M x) ,_) (FR.+-identityʳ (proj₂ (M x)))

⊙-identityʳ : (M : Op n) → (M ⊙ Idₒ) ≐ M
⊙-identityʳ M x = cong (proj₁ (M x) ,_) (FR.+-identityˡ (proj₂ (M x)))

-- The monoid of operators on n wires, under pointwise equality.
Op-monoid : ℕ → Monoid 0ℓ 0ℓ
Op-monoid n = record
  { Carrier = Op n
  ; _≈_     = _≐_
  ; _∙_     = _⊙_
  ; ε       = Idₒ
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl  = λ {M} → ≐-refl M
          ; sym   = λ {M} {N} → ≐-sym {M = M} {N}
          ; trans = λ {M} {N} {P} → ≐-trans {M = M} {N} {P} }
        ; ∙-cong = λ {M} {M'} {N} {N'} → ⊙-cong {M = M} {M'} {N} {N'} }
      ; assoc = ⊙-assoc }
    ; identity = ⊙-identityˡ , ⊙-identityʳ }
  }

-- Iterates.
infixr 8 _^ₒ_

_^ₒ_ : Op n → ℕ → Op n
M ^ₒ zero  = Idₒ
M ^ₒ suc m = M ⊙ M ^ₒ m

------------------------------------------------------------------------
-- The gates

-- The scalar: a phase on every input.
ωₒ : Op n
ωₒ x = x , 1F

-- On wire 0: translation, multiplication by a unit, and the phases x,
-- (x choose 2), (x choose 3).
Xₒ Zₒ Sₒ Tₒ : Op (₁₊ n)
Xₒ (a ∷ x) = a + 1F ∷ x , 0F
Zₒ (a ∷ x) = a ∷ x , a
Sₒ (a ∷ x) = a ∷ x , binom2 a
Tₒ (a ∷ x) = a ∷ x , binom3 a

Mₒ : F → Op (₁₊ n)
Mₒ c (a ∷ x) = c * a ∷ x , 0F

-- On wires 0 and 1: CX adds wire 1 to wire 0.
CXₒ SWAPₒ : Op (₂₊ n)
CXₒ (a ∷ b ∷ x) = a + b ∷ b ∷ x , 0F
SWAPₒ (a ∷ b ∷ x) = b ∷ a ∷ x , 0F

------------------------------------------------------------------------
-- Shifting an operator up a wire

up : Op n → Op (₁₊ n)
up M (a ∷ x) = a ∷ proj₁ (M x) , proj₂ (M x)

up-cong : {M N : Op n} → M ≐ N → up M ≐ up N
up-cong e (a ∷ x) rewrite e x = refl

up-⊙ : (M N : Op n) → up (M ⊙ N) ≐ (up M ⊙ up N)
up-⊙ M N (a ∷ x) = refl

up-Id : up (Idₒ {n}) ≐ Idₒ
up-Id (a ∷ x) = refl

up-^ : (M : Op n) (m : ℕ) → up (M ^ₒ m) ≐ up M ^ₒ m
up-^ M zero    = up-Id
up-^ M (suc m) = ≐-trans (up-⊙ M (M ^ₒ m)) (⊙-cong (≐-refl (up M)) (up-^ M m))

------------------------------------------------------------------------
-- Iterates of the gates

-- A diagonal operator: it keeps every label, with phase φ.
Diagonal : Op n → (Labels n → F) → Set
Diagonal M φ = ∀ x → M x ≡ (x , φ x)

-- Iterating a diagonal operator multiplies its phase.
^ₒ-diagonal : {M : Op n} {φ : Labels n → F} → Diagonal M φ →
              (m : ℕ) → Diagonal (M ^ₒ m) (λ x → m ×ᶠ φ x)
^ₒ-diagonal d zero    x = refl
^ₒ-diagonal {M = M} {φ} d (suc m) x = begin
  (M ⊙ M ^ₒ m) x                                       ≡⟨ cong (λ y → proj₁ (M (proj₁ y)) , proj₂ y + proj₂ (M (proj₁ y))) (^ₒ-diagonal d m x) ⟩
  proj₁ (M x) , m ×ᶠ φ x + proj₂ (M x)                  ≡⟨ cong (λ y → proj₁ y , m ×ᶠ φ x + proj₂ y) (d x) ⟩
  x , m ×ᶠ φ x + φ x                                    ≡⟨ cong (x ,_) (FR.+-comm (m ×ᶠ φ x) (φ x)) ⟩
  x , φ x + (m ×ᶠ φ x)                                    ∎
  where open Eq.≡-Reasoning

-- Iterates of the translation and of CX.
^ₒ-X : (m : ℕ) (a : F) (x : Labels n) → (Xₒ ^ₒ m) (a ∷ x) ≡ (a + (m ×ᶠ 1F) ∷ x , m ×ᶠ 0F)
^ₒ-X zero    a x = cong (λ b → b ∷ x , 0F) (sym (FR.+-identityʳ a))
^ₒ-X (suc m) a x rewrite ^ₒ-X m a x =
  cong₂ (λ b c → b ∷ x , c)
    (trans (FR.+-assoc a (m ×ᶠ 1F) 1F) (cong (a +_) (FR.+-comm (m ×ᶠ 1F) 1F)))
    (trans (FR.+-identityʳ (m ×ᶠ 0F)) (sym (FR.+-identityˡ (m ×ᶠ 0F))))

^ₒ-CX : (m : ℕ) (a b : F) (x : Labels n) → (CXₒ ^ₒ m) (a ∷ b ∷ x) ≡ (a + (m ×ᶠ b) ∷ b ∷ x , m ×ᶠ 0F)
^ₒ-CX zero    a b x = cong (λ c → c ∷ b ∷ x , 0F) (sym (FR.+-identityʳ a))
^ₒ-CX (suc m) a b x rewrite ^ₒ-CX m a b x =
  cong₂ (λ c d → c ∷ b ∷ x , d)
    (trans (FR.+-assoc a (m ×ᶠ b) b) (cong (a +_) (FR.+-comm (m ×ᶠ b) b)))
    (trans (FR.+-identityʳ (m ×ᶠ 0F)) (sym (FR.+-identityˡ (m ×ᶠ 0F))))
