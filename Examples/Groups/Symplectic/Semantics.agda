------------------------------------------------------------------------
-- Presentations of groups
--
-- The symplectic group Sp(2n, ℤ/pℤ) (p prime).
--
-- This is the *semantic* target of the qupit-Clifford presentations in
-- Examples.Groups.Symplectic.* : the group of ℤ/pℤ-linear automorphisms
-- of the phase space (ℤ/pℤ)²ⁿ = Pauli n that preserve the symplectic
-- form sform.  The pieces are collected from the scattered definitions:
--
--   * the phase space  Pauli n            (Examples.Groups.Pauli.Semantics),
--   * the symplectic form  sform          (Examples.Groups.Pauli.Semantics),
--   * "acts symplectically" = linear + sform-preserving; every Clifford
--     circuit acts this way — its action `act` (Action.agda) is linear
--     and preserves sform (Symplectic-Derived.lemma-sform-fix).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Semantics (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles    using (Group)
open import Algebra.Structures using (IsGroup)
open import Data.Product using (_,_)
open import Data.Vec using (_∷_ ; [])
open import Function using (id ; _∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≗_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)
open import Examples.Groups.Pauli.Semantics p-2 p-prime using (Pauli ; sform ; sform1 ; _+ₚ_ ; _*ₚ_)

------------------------------------------------------------------------
-- Symplectic transformations
--
-- A symplectic transformation of the n-qupit phase space: a linear
-- automorphism of Pauli n = (ℤ/pℤ)²ⁿ preserving the symplectic form.

record Symplectic (n : ℕ) : Set where
  field
    ap        : Pauli n → Pauli n
    ap⁻¹      : Pauli n → Pauli n
    invˡ      : ∀ p → ap⁻¹ (ap p) ≡ p
    invʳ      : ∀ p → ap (ap⁻¹ p) ≡ p
    linear-+  : ∀ p q → ap (p +ₚ q) ≡ ap p +ₚ ap q
    linear-*  : ∀ k p → ap (k *ₚ p) ≡ k *ₚ ap p
    preserves : ∀ p q → sform (ap p) (ap q) ≡ sform p q

open Symplectic

-- ap is injective (its left inverse is ap⁻¹).
ap-injective : ∀ {n} (S : Symplectic n) {p q} → ap S p ≡ ap S q → p ≡ q
ap-injective S {p} {q} e =
  Eq.trans (Eq.sym (invˡ S p)) (Eq.trans (Eq.cong (ap⁻¹ S) e) (invˡ S q))

------------------------------------------------------------------------
-- Equality: two transformations agree when their actions agree.

infix 4 _≈ˢ_
_≈ˢ_ : ∀ {n} → Symplectic n → Symplectic n → Set
S ≈ˢ T = ap S ≗ ap T

------------------------------------------------------------------------
-- Group operations (under composition)

-- Identity.
εˢ : ∀ {n} → Symplectic n
εˢ = record
  { ap = id ; ap⁻¹ = id
  ; invˡ = λ _ → Eq.refl ; invʳ = λ _ → Eq.refl
  ; linear-+ = λ _ _ → Eq.refl ; linear-* = λ _ _ → Eq.refl
  ; preserves = λ _ _ → Eq.refl
  }

-- Composition (the right transformation acts first).
infixl 7 _∘ˢ_
_∘ˢ_ : ∀ {n} → Symplectic n → Symplectic n → Symplectic n
S ∘ˢ T = record
  { ap   = ap S ∘ ap T
  ; ap⁻¹ = ap⁻¹ T ∘ ap⁻¹ S
  ; invˡ = λ p → Eq.trans (Eq.cong (ap⁻¹ T) (invˡ S (ap T p))) (invˡ T p)
  ; invʳ = λ p → Eq.trans (Eq.cong (ap S) (invʳ T (ap⁻¹ S p))) (invʳ S p)
  ; linear-+ = λ p q →
      Eq.trans (Eq.cong (ap S) (linear-+ T p q)) (linear-+ S (ap T p) (ap T q))
  ; linear-* = λ k p →
      Eq.trans (Eq.cong (ap S) (linear-* T k p)) (linear-* S k (ap T p))
  ; preserves = λ p q →
      Eq.trans (preserves S (ap T p) (ap T q)) (preserves T p q)
  }

-- Inverse (linearity and form-preservation of ap⁻¹ are derived from
-- those of ap using the two round-trip laws).
infix 8 _⁻¹ˢ
_⁻¹ˢ : ∀ {n} → Symplectic n → Symplectic n
S ⁻¹ˢ = record
  { ap = ap⁻¹ S ; ap⁻¹ = ap S
  ; invˡ = invʳ S ; invʳ = invˡ S
  ; linear-+ = inv-linear-+
  ; linear-* = inv-linear-*
  ; preserves = inv-preserves
  }
  where
  inv-preserves : ∀ p q → sform (ap⁻¹ S p) (ap⁻¹ S q) ≡ sform p q
  inv-preserves p q =
    Eq.trans (Eq.sym (preserves S (ap⁻¹ S p) (ap⁻¹ S q)))
             (Eq.cong₂ sform (invʳ S p) (invʳ S q))
  inv-linear-+ : ∀ p q → ap⁻¹ S (p +ₚ q) ≡ ap⁻¹ S p +ₚ ap⁻¹ S q
  inv-linear-+ p q = ap-injective S
    (Eq.trans (invʳ S (p +ₚ q))
      (Eq.sym (Eq.trans (linear-+ S (ap⁻¹ S p) (ap⁻¹ S q))
                        (Eq.cong₂ _+ₚ_ (invʳ S p) (invʳ S q)))))
  inv-linear-* : ∀ k p → ap⁻¹ S (k *ₚ p) ≡ k *ₚ ap⁻¹ S p
  inv-linear-* k p = ap-injective S
    (Eq.trans (invʳ S (k *ₚ p))
      (Eq.sym (Eq.trans (linear-* S k (ap⁻¹ S p))
                        (Eq.cong (k *ₚ_) (invʳ S p)))))

------------------------------------------------------------------------
-- The symplectic group Sp(2n, ℤ/pℤ)

module _ (n : ℕ) where

  Sp-isGroup : IsGroup {A = Symplectic n} _≈ˢ_ _∘ˢ_ εˢ _⁻¹ˢ
  Sp-isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
            { refl  = λ _ → Eq.refl
            ; sym   = λ e p → Eq.sym (e p)
            ; trans = λ e f p → Eq.trans (e p) (f p)
            }
          ; ∙-cong = λ {S} {_} {T} {T'} e f p →
              Eq.trans (Eq.cong (ap S) (f p)) (e (ap T' p))
          }
        ; assoc = λ _ _ _ _ → Eq.refl
        }
      ; identity = (λ _ _ → Eq.refl) , (λ _ _ → Eq.refl)
      }
    ; inverse = (λ S → invˡ S) , (λ S → invʳ S)
    ; ⁻¹-cong = λ {S} {T} e p → ap-injective T
        (Eq.trans (Eq.trans (Eq.sym (e (ap⁻¹ S p))) (invʳ S p)) (Eq.sym (invʳ T p)))
    }

  Sp-group : Group 0ℓ 0ℓ
  Sp-group = record { isGroup = Sp-isGroup }


module Interpretation where

  open import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
  open Syn.Symplectic

  open Eq using (cong ; cong₂ ; sym ; trans ; module ≡-Reasoning)

  ----------------------------------------------------------------------
  -- Scalar arithmetic in ℤ/pℤ, used to prove linearity and
  -- form-preservation of the generator actions.

  -- A pure rearrangement — no cancellation — so the ring solver closes it.
  add4 : ∀ (w x y z : ℤ ₚ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
  add4 = solve p-2 4 (λ w x y z → ((w ⊕ x) ⊕ (y ⊕ z)) , ((w ⊕ y) ⊕ (x ⊕ z)))
                     (λ {_} {_} {_} {_} → Eq.refl)

  -- Identities involving cancellation need the ring lemmas (the solver
  -- cannot fire meq0 over an abstract modulus).
  neg-+ : ∀ (b d : ℤ ₚ) → - (b + d) ≡ (- b) + (- d)
  neg-+ b d = sym (-‿+-comm b d)

  neg-* : ∀ (k b : ℤ ₚ) → - (k * b) ≡ k * (- b)
  neg-* = -‿distribʳ-*

  mul-d : ∀ (k b a : ℤ ₚ) → k * b + k * a ≡ k * (b + a)
  mul-d k b a = sym (*-distribˡ-+ k b a)

  sc1 : ∀ (b a : ℤ ₚ) → (b + a) + (- a) ≡ b
  sc1 b a = trans (+-assoc b a (- a)) (trans (cong (b +_) (+-inverseʳ a)) (+-identityʳ b))

  sc2 : ∀ (b a : ℤ ₚ) → (b + (- a)) + a ≡ b
  sc2 b a = trans (+-assoc b (- a) a) (trans (cong (b +_) (+-inverseˡ a)) (+-identityʳ b))

  aux-[x-b]+[b+y] : ∀ (x b y : ℤ ₚ) → (x + - b) + (b + y) ≡ x + y
  aux-[x-b]+[b+y] x b y = begin
    (x + - b) + (b + y) ≡⟨ +-assoc x (- b) (b + y) ⟩
    x + (- b + (b + y)) ≡⟨ cong (x +_) (sym (+-assoc (- b) b y)) ⟩
    x + (- b + b + y)   ≡⟨ cong (x +_) (cong (_+ y) (+-inverseˡ b)) ⟩
    x + (₀ + y)         ≡⟨ cong (x +_) (+-identityˡ y) ⟩
    x + y ∎
    where open ≡-Reasoning

  aux-[x+b]+[-b+y] : ∀ (x b y : ℤ ₚ) → (x + b) + (- b + y) ≡ x + y
  aux-[x+b]+[-b+y] x b y = begin
    (x + b) + (- b + y) ≡⟨ +-assoc x b (- b + y) ⟩
    x + (b + (- b + y)) ≡⟨ cong (x +_) (sym (+-assoc b (- b) y)) ⟩
    x + (b + - b + y)   ≡⟨ cong (x +_) (cong (_+ y) (+-inverseʳ b)) ⟩
    x + (₀ + y)         ≡⟨ cong (x +_) (+-identityˡ y) ⟩
    x + y ∎
    where open ≡-Reasoning

  aux-4 : ∀ (x a y b z w : ℤ ₚ)
        → (x + - a + (y + b)) + (z + - b + (w + a)) ≡ (x + y + (z + w))
  aux-4 x a y b z w = begin
    (x + - a + (y + b)) + (z + - b + (w + a)) ≡⟨ cong₂ _+_ (sym (+-assoc (x + - a) y b)) (cong (_+ (w + a)) (+-comm z (- b))) ⟩
    (x + - a + y + b) + (- b + z + (w + a)) ≡⟨ cong ((x + - a + y + b) +_) (+-assoc (- b) z (w + a)) ⟩
    (x + - a + y + b) + (- b + (z + (w + a))) ≡⟨ aux-[x+b]+[-b+y] (x + - a + y) b (z + (w + a)) ⟩
    (x + - a + y) + (z + (w + a)) ≡⟨ cong (_+ (z + (w + a))) (+-assoc x (- a) y) ⟩
    (x + (- a + y)) + (z + (w + a)) ≡⟨ cong₂ _+_ (cong (x +_) (+-comm (- a) y)) (cong (z +_) (+-comm w a)) ⟩
    (x + (y + - a)) + (z + (a + w)) ≡⟨ cong₂ _+_ (sym (+-assoc x y (- a))) (sym (+-assoc z a w)) ⟩
    (x + y + - a) + (z + a + w) ≡⟨ cong (x + y + - a +_) (cong (_+ w) (+-comm z a)) ⟩
    (x + y + - a) + (a + z + w) ≡⟨ cong ((x + y + - a) +_) (+-assoc a z w) ⟩
    (x + y + - a) + (a + (z + w)) ≡⟨ aux-[x-b]+[b+y] (x + y) a (z + w) ⟩
    (x + y + (z + w)) ∎
    where open ≡-Reasoning

  -- sform on a single qupit is preserved by each 1-qupit gate at k = ₁.
  h-sf : ∀ (a b c d : ℤ ₚ) → (- (- b)) * c + (- d) * a ≡ (- a) * d + c * b
  h-sf a b c d = sym (begin
    (- a) * d + c * b ≡⟨ cong (_+ c * b) (sym (-‿distribˡ-* a d)) ⟩
    - (a * d) + c * b ≡⟨ +-comm (- (a * d)) (c * b) ⟩
    c * b + - (a * d) ≡⟨ cong₂ _+_ (*-comm c b) (cong -_ (*-comm a d)) ⟩
    b * c + - (d * a) ≡⟨ cong₂ _+_ (cong (_* c) (sym (-‿involutive b))) (-‿distribˡ-* d a) ⟩
    (- (- b)) * c + (- d) * a ∎)
    where open ≡-Reasoning

  s-sf : ∀ (a b c d : ℤ ₚ) → (- a) * (d + c) + c * (b + a) ≡ (- a) * d + c * b
  s-sf a b c d = begin
    (- a) * (d + c) + c * (b + a) ≡⟨ cong₂ _+_ (*-distribˡ-+ (- a) d c) (*-distribˡ-+ c b a) ⟩
    ((- a) * d + (- a) * c) + (c * b + c * a) ≡⟨ cong₂ _+_ (cong ((- a) * d +_) (sym (-‿distribˡ-* a c))) (+-comm (c * b) (c * a)) ⟩
    ((- a) * d + - (a * c)) + (c * a + c * b) ≡⟨ cong (((- a) * d + - (a * c)) +_) (cong (_+ c * b) (*-comm c a)) ⟩
    ((- a) * d + - (a * c)) + (a * c + c * b) ≡⟨ aux-[x-b]+[b+y] ((- a) * d) (a * c) (c * b) ⟩
    (- a) * d + c * b ∎
    where open ≡-Reasoning

  -- sform on two qupits is preserved by CZ at k = ₁.
  cz-sf : ∀ (a b a' b' c d c' d' : ℤ ₚ)
        → ((- a) * (d + c') + c * (b + a')) + ((- a') * (d' + c) + c' * (b' + a))
        ≡ ((- a) * d + c * b) + ((- a') * d' + c' * b')
  cz-sf a b a' b' c d c' d' = begin
    ((- a) * (d + c') + c * (b + a')) + ((- a') * (d' + c) + c' * (b' + a))
      ≡⟨ cong₂ _+_ (cong₂ _+_ (*-distribˡ-+ (- a) d c') (*-distribˡ-+ c b a')) (cong₂ _+_ (*-distribˡ-+ (- a') d' c) (*-distribˡ-+ c' b' a)) ⟩
    (((- a) * d + (- a) * c') + (c * b + c * a')) + (((- a') * d' + (- a') * c) + (c' * b' + c' * a))
      ≡⟨ cong₂ (λ xx yy → (((- a) * d + (- a) * c') + (c * b + xx)) + (((- a') * d' + yy) + (c' * b' + c' * a))) (*-comm c a') (sym (-‿distribˡ-* a' c)) ⟩
    (((- a) * d + (- a) * c') + (c * b + a' * c)) + (((- a') * d' + - (a' * c)) + (c' * b' + c' * a))
      ≡⟨ cong₂ (λ xx yy → (((- a) * d + xx) + (c * b + a' * c)) + (((- a') * d' + - (a' * c)) + (c' * b' + yy))) (sym (-‿distribˡ-* a c')) (*-comm c' a) ⟩
    (((- a) * d + - (a * c')) + (c * b + a' * c)) + (((- a') * d' + - (a' * c)) + (c' * b' + a * c'))
      ≡⟨ aux-4 ((- a) * d) (a * c') (c * b) (a' * c) ((- a') * d') (c' * b') ⟩
    (- a) * d + c * b + ((- a') * d' + c' * b') ∎
    where open ≡-Reasoning

  ----------------------------------------------------------------------
  -- The linear action of a generator and its inverse.
  --
  -- These are the k = ₁ instances of the qupit-Clifford symplectic
  -- action:  H : (a , b) ↦ (- b , a),  S : (a , b) ↦ (a , b + a),
  -- CZ : (a , b) (a' , b') ↦ (a , b + a') (a' , b' + a); each lifts to a
  -- higher wire through _↥ by acting on the tail.

  actg : ∀ {n} → Gen n → Pauli n → Pauli n
  actg (gate₁ H-gate)  ((a , b) ∷ ps)             = (- b , a) ∷ ps
  actg (gate₁ S-gate)  ((a , b) ∷ ps)             = (a , b + a) ∷ ps
  actg (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) = (a , b + a') ∷ (a' , b' + a) ∷ ps
  actg (g ↥)           (x ∷ ps)                   = x ∷ actg g ps

  actg⁻¹ : ∀ {n} → Gen n → Pauli n → Pauli n
  actg⁻¹ (gate₁ H-gate)  ((a , b) ∷ ps)             = (b , - a) ∷ ps
  actg⁻¹ (gate₁ S-gate)  ((a , b) ∷ ps)             = (a , b + (- a)) ∷ ps
  actg⁻¹ (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) = (a , b + (- a')) ∷ (a' , b' + (- a)) ∷ ps
  actg⁻¹ (g ↥)           (x ∷ ps)                   = x ∷ actg⁻¹ g ps

  actg-invˡ : ∀ {n} (g : Gen n) p → actg⁻¹ g (actg g p) ≡ p
  actg-invˡ (gate₁ H-gate)  ((a , b) ∷ ps)             = cong₂ _∷_ (cong₂ _,_ Eq.refl (-‿involutive b)) Eq.refl
  actg-invˡ (gate₁ S-gate)  ((a , b) ∷ ps)             = cong₂ _∷_ (cong₂ _,_ Eq.refl (sc1 b a)) Eq.refl
  actg-invˡ (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) = cong₂ _∷_ (cong₂ _,_ Eq.refl (sc1 b a')) (cong₂ _∷_ (cong₂ _,_ Eq.refl (sc1 b' a)) Eq.refl)
  actg-invˡ (g ↥)           (x ∷ ps)                   = cong₂ _∷_ Eq.refl (actg-invˡ g ps)

  actg-invʳ : ∀ {n} (g : Gen n) p → actg g (actg⁻¹ g p) ≡ p
  actg-invʳ (gate₁ H-gate)  ((a , b) ∷ ps)             = cong₂ _∷_ (cong₂ _,_ (-‿involutive a) Eq.refl) Eq.refl
  actg-invʳ (gate₁ S-gate)  ((a , b) ∷ ps)             = cong₂ _∷_ (cong₂ _,_ Eq.refl (sc2 b a)) Eq.refl
  actg-invʳ (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) = cong₂ _∷_ (cong₂ _,_ Eq.refl (sc2 b a')) (cong₂ _∷_ (cong₂ _,_ Eq.refl (sc2 b' a)) Eq.refl)
  actg-invʳ (g ↥)           (x ∷ ps)                   = cong₂ _∷_ Eq.refl (actg-invʳ g ps)

  actg-+ : ∀ {n} (g : Gen n) p q → actg g (p +ₚ q) ≡ actg g p +ₚ actg g q
  actg-+ (gate₁ H-gate)  ((a , b) ∷ ps) ((c , d) ∷ qs)             = cong₂ _∷_ (cong₂ _,_ (neg-+ b d) Eq.refl) Eq.refl
  actg-+ (gate₁ S-gate)  ((a , b) ∷ ps) ((c , d) ∷ qs)             = cong₂ _∷_ (cong₂ _,_ Eq.refl (add4 b d a c)) Eq.refl
  actg-+ (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) ((c , d) ∷ (c' , d') ∷ qs)
    = cong₂ _∷_ (cong₂ _,_ Eq.refl (add4 b d a' c')) (cong₂ _∷_ (cong₂ _,_ Eq.refl (add4 b' d' a c)) Eq.refl)
  actg-+ (g ↥)           (x ∷ ps) (y ∷ qs)                         = cong₂ _∷_ Eq.refl (actg-+ g ps qs)

  actg-* : ∀ {n} (g : Gen n) k p → actg g (k *ₚ p) ≡ k *ₚ actg g p
  actg-* (gate₁ H-gate)  k ((a , b) ∷ ps)             = cong₂ _∷_ (cong₂ _,_ (neg-* k b) Eq.refl) Eq.refl
  actg-* (gate₁ S-gate)  k ((a , b) ∷ ps)             = cong₂ _∷_ (cong₂ _,_ Eq.refl (mul-d k b a)) Eq.refl
  actg-* (gate₂ CZ-gate) k ((a , b) ∷ (a' , b') ∷ ps) = cong₂ _∷_ (cong₂ _,_ Eq.refl (mul-d k b a')) (cong₂ _∷_ (cong₂ _,_ Eq.refl (mul-d k b' a)) Eq.refl)
  actg-* (g ↥)           k (x ∷ ps)                   = cong₂ _∷_ Eq.refl (actg-* g k ps)

  actg-sform : ∀ {n} (g : Gen n) p q → sform (actg g p) (actg g q) ≡ sform p q
  actg-sform (gate₁ H-gate)  ((a , b) ∷ ps) ((c , d) ∷ qs) = cong₂ _+_ (h-sf a b c d) Eq.refl
  actg-sform (gate₁ S-gate)  ((a , b) ∷ ps) ((c , d) ∷ qs) = cong₂ _+_ (s-sf a b c d) Eq.refl
  actg-sform (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) ((c , d) ∷ (c' , d') ∷ qs) = begin
    ((- a) * (d + c') + c * (b + a')) + (((- a') * (d' + c) + c' * (b' + a)) + sform ps qs)
      ≡⟨ sym (+-assoc ((- a) * (d + c') + c * (b + a')) ((- a') * (d' + c) + c' * (b' + a)) (sform ps qs)) ⟩
    (((- a) * (d + c') + c * (b + a')) + ((- a') * (d' + c) + c' * (b' + a))) + sform ps qs
      ≡⟨ cong (_+ sform ps qs) (cz-sf a b a' b' c d c' d') ⟩
    (((- a) * d + c * b) + ((- a') * d' + c' * b')) + sform ps qs
      ≡⟨ +-assoc ((- a) * d + c * b) ((- a') * d' + c' * b') (sform ps qs) ⟩
    ((- a) * d + c * b) + (((- a') * d' + c' * b') + sform ps qs) ∎
    where open ≡-Reasoning
  actg-sform (g ↥)           (x ∷ ps) (y ∷ qs) = cong₂ _+_ (Eq.refl {x = sform1 x y}) (actg-sform g ps qs)

  ----------------------------------------------------------------------
  -- Denotation of a generator and of a whole circuit.

  ⟦_⟧ᵍ : ∀ {n} → Gen n → Symplectic n
  ⟦ g ⟧ᵍ = record
    { ap        = actg g
    ; ap⁻¹      = actg⁻¹ g
    ; invˡ      = actg-invˡ g
    ; invʳ      = actg-invʳ g
    ; linear-+  = actg-+ g
    ; linear-*  = actg-* g
    ; preserves = actg-sform g
    }

  -- Words are read left-to-right (matching the circuit action): w • v
  -- applies w first, so its denotation composes on the right of v.
  ⟦_⟧ : ∀ {n} → Circuit n → Symplectic n
  ⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
  ⟦ ε ⟧      = εˢ
  ⟦ w • v ⟧  = ⟦ w ⟧ ∘ˢ ⟦ v ⟧

