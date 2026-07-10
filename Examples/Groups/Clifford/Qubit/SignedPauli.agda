------------------------------------------------------------------------
-- Presentations of groups
--
-- The signed (Heisenberg) Pauli group  RP n.
--
-- This is the central extension of the phaseless Pauli group Pauli n =
-- (ℤ/pℤ × ℤ/pℤ)ⁿ by the "sign" group ℤ/pℤ, with the commutation cocycle
--
--     β (X^a Z^b) (X^c Z^d) = Σ bᵢ cᵢ         (Z_i X_i = ω X_i Z_i)
--
-- i.e. elements are (s , P) with s a phase in ℤ/pℤ and P a phaseless
-- Pauli, multiplying as
--
--     (s , P) · (s' , P') = (s + s' + β P P' , P +ₚ P').
--
-- β is biadditive, which is exactly the 2-cocycle identity, so the product
-- is associative.  The Clifford group is the group of automorphisms of
-- RP n induced by conjugation (built in later modules); the non-split
-- nature of the Clifford extension lives in this central extension.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.SignedPauli (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles using (Group)
open import Algebra.Structures using (IsGroup ; IsMonoid ; IsSemigroup ; IsMagma)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pIₙ ; _+ₚ_ ; -ₚ_
        ; +ₚ-assoc ; +ₚ-identityˡ ; +ₚ-identityʳ ; +ₚ-inverseˡ ; +ₚ-inverseʳ )

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The commutation cocycle β

-- β P Q = Σ (Z-exponent of P)ᵢ · (X-exponent of Q)ᵢ.
β : Pauli n → Pauli n → ℤ ₚ
β []             []             = ₀
β ((a , b) ∷ ps) ((c , d) ∷ qs) = b * c + β ps qs

-- A four-term commutative rearrangement, used throughout.
+-swap-middle : ∀ (w x y z : ℤ ₚ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
+-swap-middle w x y z = begin
  (w + x) + (y + z)   ≡⟨ +-assoc w x (y + z) ⟩
  w + (x + (y + z))   ≡⟨ Eq.cong (w +_) (Eq.sym (+-assoc x y z)) ⟩
  w + ((x + y) + z)   ≡⟨ Eq.cong (λ □ → w + (□ + z)) (+-comm x y) ⟩
  w + ((y + x) + z)   ≡⟨ Eq.cong (w +_) (+-assoc y x z) ⟩
  w + (y + (x + z))   ≡⟨ Eq.sym (+-assoc w y (x + z)) ⟩
  (w + y) + (x + z)   ∎
  where open Eq.≡-Reasoning

-- β vanishes on the identity Pauli, on either side.
β-εˡ : (q : Pauli n) → β pIₙ q ≡ ₀
β-εˡ []            = Eq.refl
β-εˡ ((c , d) ∷ qs) = begin
  ₀ * c + β pIₙ qs   ≡⟨ Eq.cong (_+ β pIₙ qs) (*-zeroˡ c) ⟩
  ₀ + β pIₙ qs       ≡⟨ +-identityˡ (β pIₙ qs) ⟩
  β pIₙ qs           ≡⟨ β-εˡ qs ⟩
  ₀                  ∎
  where open Eq.≡-Reasoning

β-εʳ : (p : Pauli n) → β p pIₙ ≡ ₀
β-εʳ []            = Eq.refl
β-εʳ ((a , b) ∷ ps) = begin
  b * ₀ + β ps pIₙ   ≡⟨ Eq.cong (_+ β ps pIₙ) (*-zeroʳ b) ⟩
  ₀ + β ps pIₙ       ≡⟨ +-identityˡ (β ps pIₙ) ⟩
  β ps pIₙ           ≡⟨ β-εʳ ps ⟩
  ₀                  ∎
  where open Eq.≡-Reasoning

-- β is biadditive.
β-+ˡ : (p p' q : Pauli n) → β (p +ₚ p') q ≡ β p q + β p' q
β-+ˡ []             []               []             = Eq.sym (+-identityˡ (β [] []))
β-+ˡ ((a , b) ∷ ps) ((a' , b') ∷ ps') ((c , d) ∷ qs) = begin
  (b + b') * c + β (ps +ₚ ps') qs
    ≡⟨ Eq.cong₂ _+_ (*-distribʳ-+ c b b') (β-+ˡ ps ps' qs) ⟩
  (b * c + b' * c) + (β ps qs + β ps' qs)
    ≡⟨ +-swap-middle (b * c) (b' * c) (β ps qs) (β ps' qs) ⟩
  (b * c + β ps qs) + (b' * c + β ps' qs)  ∎
  where open Eq.≡-Reasoning

β-+ʳ : (p q q' : Pauli n) → β p (q +ₚ q') ≡ β p q + β p q'
β-+ʳ []             []             []               = Eq.sym (+-identityˡ (β [] []))
β-+ʳ ((a , b) ∷ ps) ((c , d) ∷ qs) ((c' , d') ∷ qs') = begin
  b * (c + c') + β ps (qs +ₚ qs')
    ≡⟨ Eq.cong₂ _+_ (*-distribˡ-+ b c c') (β-+ʳ ps qs qs') ⟩
  (b * c + b * c') + (β ps qs + β ps qs')
    ≡⟨ +-swap-middle (b * c) (b * c') (β ps qs) (β ps qs') ⟩
  (b * c + β ps qs) + (b * c' + β ps qs')  ∎
  where open Eq.≡-Reasoning

-- Consequences: β against an additive inverse negates.
β-invˡ : (p q : Pauli n) → β (-ₚ p) q ≡ - β p q
β-invˡ p q = begin
  β (-ₚ p) q                       ≡⟨ Eq.sym (+-identityʳ (β (-ₚ p) q)) ⟩
  β (-ₚ p) q + ₀                   ≡⟨ Eq.cong (β (-ₚ p) q +_) (Eq.sym (+-inverseʳ (β p q))) ⟩
  β (-ₚ p) q + (β p q + - β p q)   ≡⟨ Eq.sym (+-assoc (β (-ₚ p) q) (β p q) (- β p q)) ⟩
  (β (-ₚ p) q + β p q) + - β p q   ≡⟨ Eq.cong (_+ - β p q) (Eq.sym (β-+ˡ (-ₚ p) p q)) ⟩
  β ((-ₚ p) +ₚ p) q + - β p q      ≡⟨ Eq.cong (λ □ → β □ q + - β p q) (+ₚ-inverseˡ p) ⟩
  β pIₙ q + - β p q                ≡⟨ Eq.cong (_+ - β p q) (β-εˡ q) ⟩
  ₀ + - β p q                      ≡⟨ +-identityˡ (- β p q) ⟩
  - β p q                          ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The group RP n

RCarrier : ℕ → Set
RCarrier n = ℤ ₚ × Pauli n

infixl 6 _·_
_·_ : RCarrier n → RCarrier n → RCarrier n
(s , P) · (s' , P') = (s + s' + β P P') , (P +ₚ P')

ε· : RCarrier n
ε· = (₀ , pIₙ)

_⁻¹· : RCarrier n → RCarrier n
(s , P) ⁻¹· = (- s + β P P) , (-ₚ P)

------------------------------------------------------------------------
-- Group laws

·-assoc : (x y z : RCarrier n) → (x · y) · z ≡ x · (y · z)
·-assoc (s , P) (t , Q) (u , R) = Eq.cong₂ _,_ sign-eq (+ₚ-assoc P Q R)
  where
  open Eq.≡-Reasoning
  sign-eq : ((s + t + β P Q) + u + β (P +ₚ Q) R)
          ≡ (s + (t + u + β Q R) + β P (Q +ₚ R))
  sign-eq = begin
    (s + t + β P Q) + u + β (P +ₚ Q) R
      ≡⟨ Eq.cong ((s + t + β P Q) + u +_) (β-+ˡ P Q R) ⟩
    (s + t + β P Q) + u + (β P R + β Q R)
      ≡⟨ Eq.cong (λ □ → □ + (β P R + β Q R)) (+-assoc (s + t) (β P Q) u) ⟩
    (s + t + (β P Q + u)) + (β P R + β Q R)
      ≡⟨ Eq.cong (λ □ → (s + t + □) + (β P R + β Q R)) (+-comm (β P Q) u) ⟩
    (s + t + (u + β P Q)) + (β P R + β Q R)
      ≡⟨ Eq.cong (λ □ → □ + (β P R + β Q R)) (Eq.sym (+-assoc (s + t) u (β P Q))) ⟩
    (s + t + u + β P Q) + (β P R + β Q R)
      ≡⟨ Eq.sym (+-assoc (s + t + u + β P Q) (β P R) (β Q R)) ⟩
    (s + t + u + β P Q) + β P R + β Q R
      ≡⟨ lemma ⟩
    s + (t + u + β Q R) + β P (Q +ₚ R) ∎
    where
    -- rearrange the six summands  s,t,u,βPQ,βPR,βQR
    lemma : (s + t + u + β P Q) + β P R + β Q R
          ≡ s + (t + u + β Q R) + β P (Q +ₚ R)
    lemma = begin
      (s + t + u + β P Q) + β P R + β Q R
        ≡⟨ Eq.cong (_+ β Q R) (+-assoc (s + t + u) (β P Q) (β P R)) ⟩
      (s + t + u + (β P Q + β P R)) + β Q R
        ≡⟨ Eq.cong (λ □ → (s + t + u + □) + β Q R) (Eq.sym (β-+ʳ P Q R)) ⟩
      (s + t + u + β P (Q +ₚ R)) + β Q R
        ≡⟨ Eq.cong (_+ β Q R) (+-comm (s + t + u) (β P (Q +ₚ R))) ⟩
      (β P (Q +ₚ R) + (s + t + u)) + β Q R
        ≡⟨ +-assoc (β P (Q +ₚ R)) (s + t + u) (β Q R) ⟩
      β P (Q +ₚ R) + ((s + t + u) + β Q R)
        ≡⟨ +-comm (β P (Q +ₚ R)) ((s + t + u) + β Q R) ⟩
      ((s + t + u) + β Q R) + β P (Q +ₚ R)
        ≡⟨ Eq.cong (_+ β P (Q +ₚ R)) (+-assoc (s + t) u (β Q R)) ⟩
      (s + t + (u + β Q R)) + β P (Q +ₚ R)
        ≡⟨ Eq.cong (λ □ → □ + β P (Q +ₚ R)) (+-assoc s t (u + β Q R)) ⟩
      (s + (t + (u + β Q R))) + β P (Q +ₚ R)
        ≡⟨ Eq.cong (λ □ → (s + □) + β P (Q +ₚ R)) (Eq.sym (+-assoc t u (β Q R))) ⟩
      s + (t + u + β Q R) + β P (Q +ₚ R) ∎

·-identityˡ : (x : RCarrier n) → ε· · x ≡ x
·-identityˡ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-identityˡ P)
  where
  open Eq.≡-Reasoning
  sign-eq : ₀ + s + β pIₙ P ≡ s
  sign-eq = begin
    ₀ + s + β pIₙ P   ≡⟨ Eq.cong (₀ + s +_) (β-εˡ P) ⟩
    ₀ + s + ₀         ≡⟨ +-identityʳ (₀ + s) ⟩
    ₀ + s             ≡⟨ +-identityˡ s ⟩
    s                 ∎

·-identityʳ : (x : RCarrier n) → x · ε· ≡ x
·-identityʳ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-identityʳ P)
  where
  open Eq.≡-Reasoning
  sign-eq : s + ₀ + β P pIₙ ≡ s
  sign-eq = begin
    s + ₀ + β P pIₙ   ≡⟨ Eq.cong (s + ₀ +_) (β-εʳ P) ⟩
    s + ₀ + ₀         ≡⟨ +-identityʳ (s + ₀) ⟩
    s + ₀             ≡⟨ +-identityʳ s ⟩
    s                 ∎

·-inverseˡ : (x : RCarrier n) → (x ⁻¹·) · x ≡ ε·
·-inverseˡ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-inverseˡ P)
  where
  open Eq.≡-Reasoning
  sign-eq : (- s + β P P) + s + β (-ₚ P) P ≡ ₀
  sign-eq = begin
    (- s + β P P) + s + β (-ₚ P) P
      ≡⟨ Eq.cong ((- s + β P P) + s +_) (β-invˡ P P) ⟩
    (- s + β P P) + s + - β P P
      ≡⟨ Eq.cong (λ □ → □ + - β P P) (+-assoc (- s) (β P P) s) ⟩
    (- s + (β P P + s)) + - β P P
      ≡⟨ Eq.cong (λ □ → (- s + □) + - β P P) (+-comm (β P P) s) ⟩
    (- s + (s + β P P)) + - β P P
      ≡⟨ Eq.cong (_+ - β P P) (Eq.sym (+-assoc (- s) s (β P P))) ⟩
    (- s + s + β P P) + - β P P
      ≡⟨ Eq.cong (λ □ → (□ + β P P) + - β P P) (+-inverseˡ s) ⟩
    (₀ + β P P) + - β P P
      ≡⟨ Eq.cong (_+ - β P P) (+-identityˡ (β P P)) ⟩
    β P P + - β P P
      ≡⟨ +-inverseʳ (β P P) ⟩
    ₀ ∎

·-inverseʳ : (x : RCarrier n) → x · (x ⁻¹·) ≡ ε·
·-inverseʳ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-inverseʳ P)
  where
  open Eq.≡-Reasoning
  sign-eq : s + (- s + β P P) + β P (-ₚ P) ≡ ₀
  sign-eq = begin
    s + (- s + β P P) + β P (-ₚ P)
      ≡⟨ Eq.cong (s + (- s + β P P) +_) β-invʳ ⟩
    s + (- s + β P P) + - β P P
      ≡⟨ Eq.cong (λ □ → □ + - β P P) (Eq.sym (+-assoc s (- s) (β P P))) ⟩
    (s + - s + β P P) + - β P P
      ≡⟨ Eq.cong (λ □ → (□ + β P P) + - β P P) (+-inverseʳ s) ⟩
    (₀ + β P P) + - β P P
      ≡⟨ Eq.cong (_+ - β P P) (+-identityˡ (β P P)) ⟩
    β P P + - β P P
      ≡⟨ +-inverseʳ (β P P) ⟩
    ₀ ∎
    where
    β-invʳ : β P (-ₚ P) ≡ - β P P
    β-invʳ = begin
      β P (-ₚ P)                       ≡⟨ Eq.sym (+-identityˡ (β P (-ₚ P))) ⟩
      ₀ + β P (-ₚ P)                   ≡⟨ Eq.cong (_+ β P (-ₚ P)) (Eq.sym (+-inverseˡ (β P P))) ⟩
      (- β P P + β P P) + β P (-ₚ P)   ≡⟨ +-assoc (- β P P) (β P P) (β P (-ₚ P)) ⟩
      - β P P + (β P P + β P (-ₚ P))   ≡⟨ Eq.cong (- β P P +_) (Eq.sym (β-+ʳ P P (-ₚ P))) ⟩
      - β P P + β P (P +ₚ -ₚ P)        ≡⟨ Eq.cong (λ □ → - β P P + β P □) (+ₚ-inverseʳ P) ⟩
      - β P P + β P pIₙ                ≡⟨ Eq.cong (- β P P +_) (β-εʳ P) ⟩
      - β P P + ₀                      ≡⟨ +-identityʳ (- β P P) ⟩
      - β P P                          ∎

------------------------------------------------------------------------
-- The bundled group

RP-isGroup : IsGroup (_≡_ {A = RCarrier n}) _·_ ε· _⁻¹·
RP-isGroup = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = Eq.isEquivalence
        ; ∙-cong        = λ { Eq.refl Eq.refl → Eq.refl }
        }
      ; assoc = ·-assoc
      }
    ; identity = ·-identityˡ , ·-identityʳ
    }
  ; inverse = ·-inverseˡ , ·-inverseʳ
  ; ⁻¹-cong = λ { Eq.refl → Eq.refl }
  }

RP : ℕ → Group 0ℓ 0ℓ
RP n = record { isGroup = RP-isGroup {n} }
