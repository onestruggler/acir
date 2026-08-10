------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli group with phases,  P4 n  (p = 2).
--
-- The actual n-qubit Pauli group: elements i^k X^a Z^b with k ∈ ℤ/4 the
-- phase and (a , b) = P a phaseless Pauli.  Because Z X = -X Z and -1 = i²,
--
--     (i^k P) (i^{k'} P') = i^{k + k' + 2·β P P'} (P +ₚ P'),
--     β (X^a Z^b) (X^c Z^d) = Σ bᵢ cᵢ  (mod 2).
--
-- 2·β is the ℤ/4-valued commutation cocycle: the ×2 image (ι) of the
-- biadditive ℤ/2 form β, hence itself biadditive — the 2-cocycle identity —
-- so the product is associative.  The centre is ⟨i⟩ = ℤ/4; the Clifford
-- group is the group of automorphisms of P4 n fixing the centre (built in
-- later modules), and the non-split S² = Z obstruction lives here.
--
-- (The construction needs the ℤ/4 phase, not merely ℤ/2: conjugation by the
-- phase gate gives S X S⁻¹ = i X Z, so a genuine i appears.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Pauli.Qubit.SignedPauli where

open import Algebra.Bundles using (Group)
open import Algebra.Structures using (IsGroup)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Data.Fin.Mod

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open PrimeModulus p-2 p-prime

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pIₙ ; _+ₚ_ ; -ₚ_
        ; +ₚ-assoc ; +ₚ-identityˡ ; +ₚ-identityʳ ; +ₚ-inverseˡ ; +ₚ-inverseʳ )

private
  variable
    n : ℕ

-- ℤ/2 (the Pauli exponents, = ℤ ₚ) and ℤ/4 (the phase).
Φ : Set
Φ = ℤ 4

------------------------------------------------------------------------
-- A generic four-term commutative rearrangement (any modulus).

+-swap-middle : ∀ {m} (w x y z : ℤ m) → (w + x) + (y + z) ≡ (w + y) + (x + z)
+-swap-middle w x y z = begin
  (w + x) + (y + z)   ≡⟨ +-assoc w x (y + z) ⟩
  w + (x + (y + z))   ≡⟨ Eq.cong (w +_) (Eq.sym (+-assoc x y z)) ⟩
  w + ((x + y) + z)   ≡⟨ Eq.cong (λ □ → w + (□ + z)) (+-comm x y) ⟩
  w + ((y + x) + z)   ≡⟨ Eq.cong (w +_) (+-assoc y x z) ⟩
  w + (y + (x + z))   ≡⟨ Eq.sym (+-assoc w y (x + z)) ⟩
  (w + y) + (x + z)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The ℤ/2 commutation form β

-- β P Q = Σ (Z-exponent of P)ᵢ · (X-exponent of Q)ᵢ  (in ℤ ₚ = ℤ/2).
β : Pauli n → Pauli n → ℤ ₚ
β []             []             = ₀
β ((a , b) ∷ ps) ((c , d) ∷ qs) = b * c + β ps qs

β-εˡ : (q : Pauli n) → β pIₙ q ≡ ₀
β-εˡ []             = Eq.refl
β-εˡ ((c , d) ∷ qs) = begin
  ₀ * c + β pIₙ qs   ≡⟨ Eq.cong (_+ β pIₙ qs) (*-zeroˡ c) ⟩
  ₀ + β pIₙ qs       ≡⟨ +-identityˡ (β pIₙ qs) ⟩
  β pIₙ qs           ≡⟨ β-εˡ qs ⟩
  ₀                  ∎
  where open Eq.≡-Reasoning

β-εʳ : (p : Pauli n) → β p pIₙ ≡ ₀
β-εʳ []             = Eq.refl
β-εʳ ((a , b) ∷ ps) = begin
  b * ₀ + β ps pIₙ   ≡⟨ Eq.cong (_+ β ps pIₙ) (*-zeroʳ b) ⟩
  ₀ + β ps pIₙ       ≡⟨ +-identityˡ (β ps pIₙ) ⟩
  β ps pIₙ           ≡⟨ β-εʳ ps ⟩
  ₀                  ∎
  where open Eq.≡-Reasoning

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

------------------------------------------------------------------------
-- The ×2 embedding ι : ℤ/2 → ℤ/4 and the ℤ/4 cocycle γ = ι ∘ β

ι : ℤ ₚ → Φ
ι ₀ = ₀
ι ₁ = ₂

ι-+ : (x y : ℤ ₚ) → ι (x + y) ≡ ι x + ι y
ι-+ ₀ ₀ = Eq.refl
ι-+ ₀ ₁ = Eq.refl
ι-+ ₁ ₀ = Eq.refl
ι-+ ₁ ₁ = Eq.refl

γ : Pauli n → Pauli n → Φ
γ P Q = ι (β P Q)

γ-εˡ : (q : Pauli n) → γ pIₙ q ≡ ₀
γ-εˡ q = Eq.cong ι (β-εˡ q)

γ-εʳ : (p : Pauli n) → γ p pIₙ ≡ ₀
γ-εʳ p = Eq.cong ι (β-εʳ p)

γ-+ˡ : (p p' q : Pauli n) → γ (p +ₚ p') q ≡ γ p q + γ p' q
γ-+ˡ p p' q = Eq.trans (Eq.cong ι (β-+ˡ p p' q)) (ι-+ (β p q) (β p' q))

γ-+ʳ : (p q q' : Pauli n) → γ p (q +ₚ q') ≡ γ p q + γ p q'
γ-+ʳ p q q' = Eq.trans (Eq.cong ι (β-+ʳ p q q')) (ι-+ (β p q) (β p q'))

γ-invˡ : (p q : Pauli n) → γ (-ₚ p) q ≡ - γ p q
γ-invˡ p q = begin
  γ (-ₚ p) q                       ≡⟨ Eq.sym (+-identityʳ (γ (-ₚ p) q)) ⟩
  γ (-ₚ p) q + ₀                   ≡⟨ Eq.cong (γ (-ₚ p) q +_) (Eq.sym (+-inverseʳ (γ p q))) ⟩
  γ (-ₚ p) q + (γ p q + - γ p q)   ≡⟨ Eq.sym (+-assoc (γ (-ₚ p) q) (γ p q) (- γ p q)) ⟩
  (γ (-ₚ p) q + γ p q) + - γ p q   ≡⟨ Eq.cong (_+ - γ p q) (Eq.sym (γ-+ˡ (-ₚ p) p q)) ⟩
  γ ((-ₚ p) +ₚ p) q + - γ p q      ≡⟨ Eq.cong (λ □ → γ □ q + - γ p q) (+ₚ-inverseˡ p) ⟩
  γ pIₙ q + - γ p q                ≡⟨ Eq.cong (_+ - γ p q) (γ-εˡ q) ⟩
  ₀ + - γ p q                      ≡⟨ +-identityˡ (- γ p q) ⟩
  - γ p q                          ∎
  where open Eq.≡-Reasoning

γ-invʳ : (p q : Pauli n) → γ p (-ₚ q) ≡ - γ p q
γ-invʳ p q = begin
  γ p (-ₚ q)                       ≡⟨ Eq.sym (+-identityˡ (γ p (-ₚ q))) ⟩
  ₀ + γ p (-ₚ q)                   ≡⟨ Eq.cong (_+ γ p (-ₚ q)) (Eq.sym (+-inverseˡ (γ p q))) ⟩
  (- γ p q + γ p q) + γ p (-ₚ q)   ≡⟨ +-assoc (- γ p q) (γ p q) (γ p (-ₚ q)) ⟩
  - γ p q + (γ p q + γ p (-ₚ q))   ≡⟨ Eq.cong (- γ p q +_) (Eq.sym (γ-+ʳ p q (-ₚ q))) ⟩
  - γ p q + γ p (q +ₚ -ₚ q)        ≡⟨ Eq.cong (λ □ → - γ p q + γ p □) (+ₚ-inverseʳ q) ⟩
  - γ p q + γ p pIₙ                ≡⟨ Eq.cong (- γ p q +_) (γ-εʳ p) ⟩
  - γ p q + ₀                      ≡⟨ +-identityʳ (- γ p q) ⟩
  - γ p q                          ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The group P4 n

P4Carrier : ℕ → Set
P4Carrier n = Φ × Pauli n

infixl 6 _·_
_·_ : P4Carrier n → P4Carrier n → P4Carrier n
(s , P) · (s' , P') = (s + s' + γ P P') , (P +ₚ P')

ε· : P4Carrier n
ε· = (₀ , pIₙ)

_⁻¹· : P4Carrier n → P4Carrier n
(s , P) ⁻¹· = (- s + γ P P) , (-ₚ P)

------------------------------------------------------------------------
-- Group laws

·-assoc : (x y z : P4Carrier n) → (x · y) · z ≡ x · (y · z)
·-assoc (s , P) (t , Q) (u , R) = Eq.cong₂ _,_ sign-eq (+ₚ-assoc P Q R)
  where
  open Eq.≡-Reasoning
  sign-eq : ((s + t + γ P Q) + u + γ (P +ₚ Q) R)
          ≡ (s + (t + u + γ Q R) + γ P (Q +ₚ R))
  sign-eq = begin
    (s + t + γ P Q) + u + γ (P +ₚ Q) R
      ≡⟨ Eq.cong ((s + t + γ P Q) + u +_) (γ-+ˡ P Q R) ⟩
    (s + t + γ P Q) + u + (γ P R + γ Q R)
      ≡⟨ Eq.cong (λ □ → □ + (γ P R + γ Q R)) (+-assoc (s + t) (γ P Q) u) ⟩
    (s + t + (γ P Q + u)) + (γ P R + γ Q R)
      ≡⟨ Eq.cong (λ □ → (s + t + □) + (γ P R + γ Q R)) (+-comm (γ P Q) u) ⟩
    (s + t + (u + γ P Q)) + (γ P R + γ Q R)
      ≡⟨ Eq.cong (λ □ → □ + (γ P R + γ Q R)) (Eq.sym (+-assoc (s + t) u (γ P Q))) ⟩
    (s + t + u + γ P Q) + (γ P R + γ Q R)
      ≡⟨ Eq.sym (+-assoc (s + t + u + γ P Q) (γ P R) (γ Q R)) ⟩
    (s + t + u + γ P Q) + γ P R + γ Q R
      ≡⟨ lemma ⟩
    s + (t + u + γ Q R) + γ P (Q +ₚ R) ∎
    where
    lemma : (s + t + u + γ P Q) + γ P R + γ Q R
          ≡ s + (t + u + γ Q R) + γ P (Q +ₚ R)
    lemma = begin
      (s + t + u + γ P Q) + γ P R + γ Q R
        ≡⟨ Eq.cong (_+ γ Q R) (+-assoc (s + t + u) (γ P Q) (γ P R)) ⟩
      (s + t + u + (γ P Q + γ P R)) + γ Q R
        ≡⟨ Eq.cong (λ □ → (s + t + u + □) + γ Q R) (Eq.sym (γ-+ʳ P Q R)) ⟩
      (s + t + u + γ P (Q +ₚ R)) + γ Q R
        ≡⟨ Eq.cong (_+ γ Q R) (+-comm (s + t + u) (γ P (Q +ₚ R))) ⟩
      (γ P (Q +ₚ R) + (s + t + u)) + γ Q R
        ≡⟨ +-assoc (γ P (Q +ₚ R)) (s + t + u) (γ Q R) ⟩
      γ P (Q +ₚ R) + ((s + t + u) + γ Q R)
        ≡⟨ +-comm (γ P (Q +ₚ R)) ((s + t + u) + γ Q R) ⟩
      ((s + t + u) + γ Q R) + γ P (Q +ₚ R)
        ≡⟨ Eq.cong (_+ γ P (Q +ₚ R)) (+-assoc (s + t) u (γ Q R)) ⟩
      (s + t + (u + γ Q R)) + γ P (Q +ₚ R)
        ≡⟨ Eq.cong (λ □ → □ + γ P (Q +ₚ R)) (+-assoc s t (u + γ Q R)) ⟩
      (s + (t + (u + γ Q R))) + γ P (Q +ₚ R)
        ≡⟨ Eq.cong (λ □ → (s + □) + γ P (Q +ₚ R)) (Eq.sym (+-assoc t u (γ Q R))) ⟩
      s + (t + u + γ Q R) + γ P (Q +ₚ R) ∎

·-identityˡ : (x : P4Carrier n) → ε· · x ≡ x
·-identityˡ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-identityˡ P)
  where
  open Eq.≡-Reasoning
  sign-eq : ₀ + s + γ pIₙ P ≡ s
  sign-eq = begin
    ₀ + s + γ pIₙ P   ≡⟨ Eq.cong (₀ + s +_) (γ-εˡ P) ⟩
    ₀ + s + ₀         ≡⟨ +-identityʳ (₀ + s) ⟩
    ₀ + s             ≡⟨ +-identityˡ s ⟩
    s                 ∎

·-identityʳ : (x : P4Carrier n) → x · ε· ≡ x
·-identityʳ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-identityʳ P)
  where
  open Eq.≡-Reasoning
  sign-eq : s + ₀ + γ P pIₙ ≡ s
  sign-eq = begin
    s + ₀ + γ P pIₙ   ≡⟨ Eq.cong (s + ₀ +_) (γ-εʳ P) ⟩
    s + ₀ + ₀         ≡⟨ +-identityʳ (s + ₀) ⟩
    s + ₀             ≡⟨ +-identityʳ s ⟩
    s                 ∎

·-inverseˡ : (x : P4Carrier n) → (x ⁻¹·) · x ≡ ε·
·-inverseˡ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-inverseˡ P)
  where
  open Eq.≡-Reasoning
  sign-eq : (- s + γ P P) + s + γ (-ₚ P) P ≡ ₀
  sign-eq = begin
    (- s + γ P P) + s + γ (-ₚ P) P
      ≡⟨ Eq.cong ((- s + γ P P) + s +_) (γ-invˡ P P) ⟩
    (- s + γ P P) + s + - γ P P
      ≡⟨ Eq.cong (λ □ → □ + - γ P P) (+-assoc (- s) (γ P P) s) ⟩
    (- s + (γ P P + s)) + - γ P P
      ≡⟨ Eq.cong (λ □ → (- s + □) + - γ P P) (+-comm (γ P P) s) ⟩
    (- s + (s + γ P P)) + - γ P P
      ≡⟨ Eq.cong (_+ - γ P P) (Eq.sym (+-assoc (- s) s (γ P P))) ⟩
    (- s + s + γ P P) + - γ P P
      ≡⟨ Eq.cong (λ □ → (□ + γ P P) + - γ P P) (+-inverseˡ s) ⟩
    (₀ + γ P P) + - γ P P
      ≡⟨ Eq.cong (_+ - γ P P) (+-identityˡ (γ P P)) ⟩
    γ P P + - γ P P
      ≡⟨ +-inverseʳ (γ P P) ⟩
    ₀ ∎

·-inverseʳ : (x : P4Carrier n) → x · (x ⁻¹·) ≡ ε·
·-inverseʳ (s , P) = Eq.cong₂ _,_ sign-eq (+ₚ-inverseʳ P)
  where
  open Eq.≡-Reasoning
  sign-eq : s + (- s + γ P P) + γ P (-ₚ P) ≡ ₀
  sign-eq = begin
    s + (- s + γ P P) + γ P (-ₚ P)
      ≡⟨ Eq.cong (s + (- s + γ P P) +_) (γ-invʳ P P) ⟩
    s + (- s + γ P P) + - γ P P
      ≡⟨ Eq.cong (λ □ → □ + - γ P P) (Eq.sym (+-assoc s (- s) (γ P P))) ⟩
    (s + - s + γ P P) + - γ P P
      ≡⟨ Eq.cong (λ □ → (□ + γ P P) + - γ P P) (+-inverseʳ s) ⟩
    (₀ + γ P P) + - γ P P
      ≡⟨ Eq.cong (_+ - γ P P) (+-identityˡ (γ P P)) ⟩
    γ P P + - γ P P
      ≡⟨ +-inverseʳ (γ P P) ⟩
    ₀ ∎

------------------------------------------------------------------------
-- The bundled group

P4-isGroup : IsGroup (_≡_ {A = P4Carrier n}) _·_ ε· _⁻¹·
P4-isGroup = record
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

P4 : ℕ → Group 0ℓ 0ℓ
P4 n = record { isGroup = P4-isGroup {n} }
