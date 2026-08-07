------------------------------------------------------------------------
-- Presentations of groups
--
-- The projective qubit Clifford group built from the projective Pauli
-- group V = Pauli n and the symplectic group Sp(2n,2)  (p = 2).
--
-- An element is a PAIR (S , φ): a symplectic map S of the phase space
-- together with the phase function φ recording what conjugation does to
-- the Pauli basis,
--
--     C W(v) C⁻¹ = i^(φ v) W(S v),     W(a , b) = X^a Z^b.
--
-- The phase must be ℤ/4-valued, not ℤ/2-valued: S X S⁻¹ = i X Z.  The two
-- components are not independent.  Writing the commutation cocycle of the
-- basis as
--
--     W(v) W(w) = i^(γ v w) W(v +ₚ w),    γ v w = ι (β v w),
--
-- applying C to that identity forces φ to be a QUADRATIC REFINEMENT of the
-- defect of γ along S:
--
--     φ (v +ₚ w) = φ v + φ w + δ S v w,   δ S v w = γ (S v) (S w) − γ v w.
--
-- (γ is 2-torsion, being ×2 of a ℤ/2 form, so the difference is written
-- below as a sum.)  That constraint IS the twist: it is why the group of
-- pairs is not the semidirect product V ⋊ Sp — the sign functions
-- admissible for S form a torsor over Hom(V , ℤ/2) ≅ V, not a subgroup
-- containing φ = 0 for every S.  Multiplication follows from composing
-- two conjugations:
--
--     (S₁ , φ₁) ∙ (S₂ , φ₂) = (S₁ ∘ S₂ , λ v → φ₂ v + φ₁ (S₂ v)).
--
-- The proof obligation for the product is the CHAIN RULE δ-∘ for the
-- twist; for the inverse it is that δ is 2-torsion and symmetric under
-- S ↦ S⁻¹.  Everything else is ℤ/4 rearrangement.
--
-- This module is deliberately self-contained: it shares only the phase
-- space (Pauli.Semantics) and the symplectic group (Symplectic.Semantics)
-- with the rest of the development, and in particular does not go through
-- the word-based Clifford group of Qubit.CliffordGroup.  The commutation
-- cocycle β / ι / γ is re-derived here rather than imported.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.VSp where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Algebra.Structures using (IsGroup)
open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; Σ-syntax)
open import Data.Vec using ([] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≗_)
open import Relation.Nullary.Decidable using (from-yes)

open import Notations
open import Zp.ModularArithmetic

open import ForStdlib.Algebra.Construct.Extension using (Extension)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

-- Qubit case: the prime is 2.
p-2 : ℕ
p-2 = 0

p-prime : Prime 2
p-prime = from-yes (prime? 2)

open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pI ; pX ; pZ ; pIₙ ; sform ; sform1
        ; _+₁_ ; _+ₚ_ ; -ₚ_ ; +₁-identityʳ
        ; +ₚ-assoc ; +ₚ-identityˡ ; +ₚ-identityʳ ; +ₚ-inverseʳ ; +ₚ-group )
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; ap-injective ; _≈ˢ_ ; _∘ˢ_ ; εˢ ; _⁻¹ˢ ; Sp-group)
open Symplectic using (ap ; ap⁻¹ ; invˡ ; invʳ ; linear-+)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic
  using (Gen ; Circuit ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg ; ⟦_⟧ᵍ ; ⟦_⟧)
open import Examples.Groups.Symplectic.Surjectivity p-2 p-prime using (surj-nf)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The phase group ℤ/4

Φ : Set
Φ = ℤ 4

-- Pure rearrangements of ℤ/4 sums, by the ring solver at modulus 4.

shuffle-mid : (x z y : Φ) → (x + z) + (z + y) ≡ (x + y) + (z + z)
shuffle-mid = solve 2 3 (λ x z y → ((x ⊕ z) ⊕ (z ⊕ y)) , ((x ⊕ y) ⊕ (z ⊕ z)))
                        (λ {_} {_} {_} → Eq.refl)

swap4 : (w x y z : Φ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
swap4 = solve 2 4 (λ w x y z → ((w ⊕ x) ⊕ (y ⊕ z)) , ((w ⊕ y) ⊕ (x ⊕ z)))
                  (λ {_} {_} {_} {_} → Eq.refl)

shuffle6 : (a b c d e f : Φ) →
           ((a + b) + c) + ((d + e) + f) ≡ ((a + d) + (b + e)) + (f + c)
shuffle6 = solve 2 6 (λ a b c d e f →
             (((a ⊕ b) ⊕ c) ⊕ ((d ⊕ e) ⊕ f)) , (((a ⊕ d) ⊕ (b ⊕ e)) ⊕ (f ⊕ c)))
             (λ {_} {_} {_} {_} {_} {_} → Eq.refl)

neg-3 : (a b c : Φ) → - ((a + b) + c) ≡ ((- a) + (- b)) + (- c)
neg-3 = solve 2 3 (λ a b c → (⊝ ((a ⊕ b) ⊕ c)) , ((⊝ a ⊕ ⊝ b) ⊕ ⊝ c))
                  (λ {_} {_} {_} → Eq.refl)

-- On a 2-torsion element negation is the identity.
neg-2tors : (x : Φ) → x + x ≡ ₀ → - x ≡ x
neg-2tors x hx = begin
  - x             ≡⟨ Eq.sym (+-identityʳ (- x)) ⟩
  - x + ₀         ≡⟨ Eq.cong (- x +_) (Eq.sym hx) ⟩
  - x + (x + x)   ≡⟨ Eq.sym (+-assoc (- x) x x) ⟩
  (- x + x) + x   ≡⟨ Eq.cong (_+ x) (+-inverseˡ x) ⟩
  ₀ + x           ≡⟨ +-identityˡ x ⟩
  x               ∎
  where open Eq.≡-Reasoning

-- A sum of 2-torsion elements is 2-torsion.
+-2tors : (x y : Φ) → x + x ≡ ₀ → y + y ≡ ₀ → (x + y) + (x + y) ≡ ₀
+-2tors x y hx hy = begin
  (x + y) + (x + y)   ≡⟨ swap4 x y x y ⟩
  (x + x) + (y + y)   ≡⟨ Eq.cong₂ _+_ hx hy ⟩
  ₀ + ₀               ≡⟨ +-identityˡ ₀ ⟩
  ₀                   ∎
  where open Eq.≡-Reasoning

-- Cancelling a 2-torsion element sitting in the middle of a sum.
mid-cancel : (x z y : Φ) → z + z ≡ ₀ → (x + z) + (z + y) ≡ x + y
mid-cancel x z y hz = begin
  (x + z) + (z + y)   ≡⟨ shuffle-mid x z y ⟩
  (x + y) + (z + z)   ≡⟨ Eq.cong ((x + y) +_) hz ⟩
  (x + y) + ₀         ≡⟨ +-identityʳ (x + y) ⟩
  x + y               ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The commutation cocycle of the Pauli basis
--
-- W(a , b) = X^a Z^b, so pushing the second word past the first costs one
-- sign per Z-over-X crossing:  β v w = Σ bᵢ cᵢ  in ℤ/2, and the phase is
-- its ×2 image in ℤ/4.

-- ι : ℤ/2 → ℤ/4, multiplication by 2.
ι : ℤ ₚ → Φ
ι ₀ = ₀
ι ₁ = ₂

ι-+ : (x y : ℤ ₚ) → ι (x + y) ≡ ι x + ι y
ι-+ ₀ ₀ = auto
ι-+ ₀ ₁ = auto
ι-+ ₁ ₀ = auto
ι-+ ₁ ₁ = auto

-- Everything in the image of ι has order dividing 2.
ι-2 : (x : ℤ ₚ) → ι x + ι x ≡ ₀
ι-2 ₀ = auto
ι-2 ₁ = auto

β : Pauli n → Pauli n → ℤ ₚ
β []             []             = ₀
β ((a , b) ∷ ps) ((c , d) ∷ qs) = b * c + β ps qs

γ : Pauli n → Pauli n → Φ
γ v w = ι (β v w)

γ-2 : (v w : Pauli n) → γ v w + γ v w ≡ ₀
γ-2 v w = ι-2 (β v w)

------------------------------------------------------------------------
-- The twist of a symplectic map
--
-- δ S v w = γ (S v) (S w) − γ v w, the failure of S to preserve the
-- commutation cocycle.  Since γ is 2-torsion the difference is a sum.

δ : Symplectic n → Pauli n → Pauli n → Φ
δ S v w = γ (ap S v) (ap S w) + γ v w

δ-2 : (S : Symplectic n) (v w : Pauli n) → δ S v w + δ S v w ≡ ₀
δ-2 S v w = +-2tors (γ (ap S v) (ap S w)) (γ v w)
                    (γ-2 (ap S v) (ap S w)) (γ-2 v w)

-- Negation acts trivially on twists.
δ-neg : (S : Symplectic n) (v w : Pauli n) → - δ S v w ≡ δ S v w
δ-neg S v w = neg-2tors (δ S v w) (δ-2 S v w)

-- The identity has no twist.
δ-ε : (v w : Pauli n) → δ εˢ v w ≡ ₀
δ-ε v w = γ-2 v w

-- Equal actions, equal twists.
δ-cong : {S T : Symplectic n} → S ≈ˢ T → (v w : Pauli n) → δ S v w ≡ δ T v w
δ-cong S≈T v w = Eq.cong₂ (λ x y → γ x y + γ v w) (S≈T v) (S≈T w)

-- The chain rule: the twist of a composite is the twist of the outer map
-- (measured downstream) plus the twist of the inner one.  This is what
-- makes the multiplication below associative-with-action, i.e. a group.
δ-∘ : (S T : Symplectic n) (v w : Pauli n) →
      δ (S ∘ˢ T) v w ≡ δ S (ap T v) (ap T w) + δ T v w
δ-∘ S T v w = Eq.sym (begin
  (γ (ap S (ap T v)) (ap S (ap T w)) + γ (ap T v) (ap T w))
    + (γ (ap T v) (ap T w) + γ v w)
      ≡⟨ mid-cancel (γ (ap S (ap T v)) (ap S (ap T w)))
                    (γ (ap T v) (ap T w)) (γ v w) (γ-2 (ap T v) (ap T w)) ⟩
  γ (ap S (ap T v)) (ap S (ap T w)) + γ v w   ∎)
  where open Eq.≡-Reasoning

-- Transporting a twist through S⁻¹.
δ-⁻¹ : (S : Symplectic n) (v w : Pauli n) →
       δ S (ap⁻¹ S v) (ap⁻¹ S w) ≡ δ (S ⁻¹ˢ) v w
δ-⁻¹ S v w = begin
  γ (ap S (ap⁻¹ S v)) (ap S (ap⁻¹ S w)) + γ (ap⁻¹ S v) (ap⁻¹ S w)
    ≡⟨ Eq.cong₂ (λ x y → γ x y + γ (ap⁻¹ S v) (ap⁻¹ S w)) (invʳ S v) (invʳ S w) ⟩
  γ v w + γ (ap⁻¹ S v) (ap⁻¹ S w)
    ≡⟨ +-comm (γ v w) (γ (ap⁻¹ S v) (ap⁻¹ S w)) ⟩
  γ (ap⁻¹ S v) (ap⁻¹ S w) + γ v w   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The group of pairs
--
-- A projective Clifford is a symplectic map together with a phase
-- function refining its twist.

IsRefinement : (S : Symplectic n) (φ : Pauli n → Φ) → Set
IsRefinement {n} S φ = (v w : Pauli n) → φ (v +ₚ w) ≡ φ v + φ w + δ S v w

record Cliff (n : ℕ) : Set where
  field
    symp    : Symplectic n
    phase   : Pauli n → Φ
    refines : IsRefinement symp phase

open Cliff public

------------------------------------------------------------------------
-- Equality: same symplectic action, same phases

infix 4 _≈ᵛ_
_≈ᵛ_ : Cliff n → Cliff n → Set
X ≈ᵛ Y = (symp X ≈ˢ symp Y) × (phase X ≗ phase Y)

≈ᵛ-isEquivalence : IsEquivalence (_≈ᵛ_ {n})
≈ᵛ-isEquivalence = record
  { refl  = (λ _ → Eq.refl) , (λ _ → Eq.refl)
  ; sym   = λ { (s , f) → (λ v → Eq.sym (s v)) , (λ v → Eq.sym (f v)) }
  ; trans = λ { (s , f) (s' , f') → (λ v → Eq.trans (s v) (s' v))
                                  , (λ v → Eq.trans (f v) (f' v)) }
  }

------------------------------------------------------------------------
-- Multiplication
--
-- (S₁ , φ₁) ∙ (S₂ , φ₂) = (S₁ ∘ S₂ , λ v → φ₂ v + φ₁ (S₂ v)):  conjugate
-- by the right factor first, then by the left, accumulating phases.

infixl 7 _∙ᵛ_
_∙ᵛ_ : Cliff n → Cliff n → Cliff n
X ∙ᵛ Y = record { symp = S ∘ˢ T ; phase = ψ' ; refines = prf }
  where
  open Eq.≡-Reasoning
  S = symp X ; T = symp Y
  φ = phase X ; ψ = phase Y
  ψ' = λ v → ψ v + φ (ap T v)

  prf : IsRefinement (S ∘ˢ T) ψ'
  prf v w = begin
    ψ (v +ₚ w) + φ (ap T (v +ₚ w))
      ≡⟨ Eq.cong₂ _+_ (refines Y v w) (Eq.cong φ (linear-+ T v w)) ⟩
    ((ψ v + ψ w) + δ T v w) + φ (ap T v +ₚ ap T w)
      ≡⟨ Eq.cong (((ψ v + ψ w) + δ T v w) +_) (refines X (ap T v) (ap T w)) ⟩
    ((ψ v + ψ w) + δ T v w)
      + ((φ (ap T v) + φ (ap T w)) + δ S (ap T v) (ap T w))
      ≡⟨ shuffle6 (ψ v) (ψ w) (δ T v w)
                  (φ (ap T v)) (φ (ap T w)) (δ S (ap T v) (ap T w)) ⟩
    (ψ' v + ψ' w) + (δ S (ap T v) (ap T w) + δ T v w)
      ≡⟨ Eq.cong ((ψ' v + ψ' w) +_) (Eq.sym (δ-∘ S T v w)) ⟩
    (ψ' v + ψ' w) + δ (S ∘ˢ T) v w   ∎

------------------------------------------------------------------------
-- Identity: the identity map with no phase

εᵛ : Cliff n
εᵛ = record { symp = εˢ ; phase = λ _ → ₀ ; refines = prf }
  where
  open Eq.≡-Reasoning
  prf : IsRefinement {n} εˢ (λ _ → ₀)
  prf v w = Eq.sym (begin
    (₀ + ₀) + δ εˢ v w   ≡⟨ Eq.cong ((₀ + ₀) +_) (δ-ε v w) ⟩
    (₀ + ₀) + ₀          ≡⟨ +-identityʳ (₀ + ₀) ⟩
    ₀ + ₀                ≡⟨ +-identityˡ ₀ ⟩
    ₀                    ∎)

------------------------------------------------------------------------
-- Inverse
--
-- Undo the symplectic map and negate the phase it collected.

infix 8 _⁻¹ᵛ
_⁻¹ᵛ : Cliff n → Cliff n
X ⁻¹ᵛ = record { symp = S ⁻¹ˢ ; phase = χ ; refines = prf }
  where
  open Eq.≡-Reasoning
  S = symp X ; φ = phase X
  χ = λ v → - φ (ap⁻¹ S v)

  prf : IsRefinement (S ⁻¹ˢ) χ
  prf v w = begin
    - φ (ap⁻¹ S (v +ₚ w))
      ≡⟨ Eq.cong (λ □ → - φ □) (linear-+ (S ⁻¹ˢ) v w) ⟩
    - φ (ap⁻¹ S v +ₚ ap⁻¹ S w)
      ≡⟨ Eq.cong -_ (refines X (ap⁻¹ S v) (ap⁻¹ S w)) ⟩
    - ((φ (ap⁻¹ S v) + φ (ap⁻¹ S w)) + δ S (ap⁻¹ S v) (ap⁻¹ S w))
      ≡⟨ neg-3 (φ (ap⁻¹ S v)) (φ (ap⁻¹ S w)) (δ S (ap⁻¹ S v) (ap⁻¹ S w)) ⟩
    (χ v + χ w) + - δ S (ap⁻¹ S v) (ap⁻¹ S w)
      ≡⟨ Eq.cong ((χ v + χ w) +_) (δ-neg S (ap⁻¹ S v) (ap⁻¹ S w)) ⟩
    (χ v + χ w) + δ S (ap⁻¹ S v) (ap⁻¹ S w)
      ≡⟨ Eq.cong ((χ v + χ w) +_) (δ-⁻¹ S v w) ⟩
    (χ v + χ w) + δ (S ⁻¹ˢ) v w   ∎

------------------------------------------------------------------------
-- The group laws
--
-- The symplectic component is inherited from Sp; the phase component is
-- ℤ/4 arithmetic.

-- ap⁻¹ is determined by ap, so it respects ≈ˢ.
ap⁻¹-cong : {S T : Symplectic n} → S ≈ˢ T → ap⁻¹ S ≗ ap⁻¹ T
ap⁻¹-cong {S = S} {T} S≈T v = ap-injective S
  (Eq.trans (invʳ S v) (Eq.trans (Eq.sym (invʳ T v)) (Eq.sym (S≈T (ap⁻¹ T v)))))

∙ᵛ-cong : {X X' Y Y' : Cliff n} → X ≈ᵛ X' → Y ≈ᵛ Y' → (X ∙ᵛ Y) ≈ᵛ (X' ∙ᵛ Y')
∙ᵛ-cong {X = X} {X'} {Y} {Y'} (s , f) (t , g) =
    (λ v → Eq.trans (Eq.cong (ap (symp X)) (t v)) (s (ap (symp Y') v)))
  , (λ v → Eq.cong₂ _+_ (g v)
             (Eq.trans (Eq.cong (phase X) (t v)) (f (ap (symp Y') v))))

∙ᵛ-assoc : (X Y Z : Cliff n) → ((X ∙ᵛ Y) ∙ᵛ Z) ≈ᵛ (X ∙ᵛ (Y ∙ᵛ Z))
∙ᵛ-assoc X Y Z = (λ _ → Eq.refl)
  , λ v → Eq.sym (+-assoc (phase Z v) (phase Y (ap (symp Z) v))
                          (phase X (ap (symp Y) (ap (symp Z) v))))

∙ᵛ-identityˡ : (X : Cliff n) → (εᵛ ∙ᵛ X) ≈ᵛ X
∙ᵛ-identityˡ X = (λ _ → Eq.refl) , λ v → +-identityʳ (phase X v)

∙ᵛ-identityʳ : (X : Cliff n) → (X ∙ᵛ εᵛ) ≈ᵛ X
∙ᵛ-identityʳ X = (λ _ → Eq.refl) , λ v → +-identityˡ (phase X v)

∙ᵛ-inverseˡ : (X : Cliff n) → ((X ⁻¹ᵛ) ∙ᵛ X) ≈ᵛ εᵛ
∙ᵛ-inverseˡ X = invˡ (symp X)
  , λ v → Eq.trans (Eq.cong (λ □ → phase X v + - phase X □) (invˡ (symp X) v))
                   (+-inverseʳ (phase X v))

∙ᵛ-inverseʳ : (X : Cliff n) → (X ∙ᵛ (X ⁻¹ᵛ)) ≈ᵛ εᵛ
∙ᵛ-inverseʳ X = invʳ (symp X)
  , λ v → +-inverseˡ (phase X (ap⁻¹ (symp X) v))

⁻¹ᵛ-cong : {X Y : Cliff n} → X ≈ᵛ Y → (X ⁻¹ᵛ) ≈ᵛ (Y ⁻¹ᵛ)
⁻¹ᵛ-cong {X = X} {Y} (s , f) = ap⁻¹-cong {S = symp X} {symp Y} s
  , λ v → Eq.cong -_ (Eq.trans (Eq.cong (phase X) (ap⁻¹-cong {S = symp X} {symp Y} s v))
                               (f (ap⁻¹ (symp Y) v)))

------------------------------------------------------------------------
-- The bundled group

VSp-isGroup : IsGroup (_≈ᵛ_ {n}) _∙ᵛ_ εᵛ _⁻¹ᵛ
VSp-isGroup = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈ᵛ-isEquivalence
        ; ∙-cong        = λ {X} {X'} {Y} {Y'} → ∙ᵛ-cong {X = X} {X'} {Y} {Y'}
        }
      ; assoc = ∙ᵛ-assoc
      }
    ; identity = ∙ᵛ-identityˡ , ∙ᵛ-identityʳ
    }
  ; inverse = ∙ᵛ-inverseˡ , ∙ᵛ-inverseʳ
  ; ⁻¹-cong = λ {X} {Y} → ⁻¹ᵛ-cong {X = X} {Y}
  }

VSp-group : ℕ → Group 0ℓ 0ℓ
VSp-group n = record { isGroup = VSp-isGroup {n} }

------------------------------------------------------------------------
-- Phase space arithmetic at p = 2
--
-- Every Pauli is its own inverse, and every symplectic map fixes the
-- origin.

neg-id : (x : ℤ ₚ) → - x ≡ x
neg-id ₀ = auto
neg-id ₁ = auto

-ₚ-id : (u : Pauli n) → -ₚ u ≡ u
-ₚ-id []             = Eq.refl
-ₚ-id ((a , b) ∷ us) = Eq.cong₂ _∷_ (Eq.cong₂ _,_ (neg-id a) (neg-id b)) (-ₚ-id us)

+ₚ-self : (u : Pauli n) → u +ₚ u ≡ pIₙ
+ₚ-self u = Eq.trans (Eq.cong (u +ₚ_) (Eq.sym (-ₚ-id u))) (+ₚ-inverseʳ u)

ap-pIₙ : (S : Symplectic n) → ap S (pIₙ {n}) ≡ pIₙ
ap-pIₙ {n} S = begin
  ap S pIₙ               ≡⟨ Eq.cong (ap S) (Eq.sym (+ₚ-self pIₙ)) ⟩
  ap S (pIₙ +ₚ pIₙ)      ≡⟨ linear-+ S pIₙ pIₙ ⟩
  ap S pIₙ +ₚ ap S pIₙ   ≡⟨ +ₚ-self (ap S pIₙ) ⟩
  pIₙ                    ∎
  where open Eq.≡-Reasoning

-- Hence the origin is untwisted, and every phase function vanishes there.
δ-pIₙ : (S : Symplectic n) → δ S (pIₙ {n}) (pIₙ {n}) ≡ ₀
δ-pIₙ {n} S rewrite ap-pIₙ S = γ-2 (pIₙ {n}) (pIₙ {n})

cancel-self : (x : Φ) → x ≡ x + x → x ≡ ₀
cancel-self ₀ e = auto
cancel-self ₁ ()
cancel-self ₂ ()
cancel-self ₃ ()

phase-ε : (X : Cliff n) → phase X (pIₙ {n}) ≡ ₀
phase-ε {n} X = cancel-self (phase X pIₙ) (begin
  phase X pIₙ
    ≡⟨ Eq.cong (phase X) (Eq.sym (+ₚ-identityˡ pIₙ)) ⟩
  phase X (pIₙ +ₚ pIₙ)
    ≡⟨ refines X pIₙ pIₙ ⟩
  (phase X pIₙ + phase X pIₙ) + δ (symp X) pIₙ pIₙ
    ≡⟨ Eq.cong ((phase X pIₙ + phase X pIₙ) +_) (δ-pIₙ (symp X)) ⟩
  (phase X pIₙ + phase X pIₙ) + ₀
    ≡⟨ +-identityʳ (phase X pIₙ + phase X pIₙ) ⟩
  phase X pIₙ + phase X pIₙ   ∎)
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Bilinearity and nondegeneracy of the symplectic form

swap4ₚ : (w x y z : ℤ ₚ) → (w + x) + (y + z) ≡ (w + y) + (x + z)
swap4ₚ = solve p-2 4 (λ w x y z → ((w ⊕ x) ⊕ (y ⊕ z)) , ((w ⊕ y) ⊕ (x ⊕ z)))
                     (λ {_} {_} {_} {_} → Eq.refl)

sform1-+ˡ : (p p' q : Pauli1) → sform1 (p +₁ p') q ≡ sform1 p q + sform1 p' q
sform1-+ˡ (a , b) (a' , b') (c , d) = lemma a b a' b' c d
  where
  lemma : (a b a' b' c d : ℤ ₚ) →
          (- (a + a')) * d + c * (b + b')
            ≡ ((- a) * d + c * b) + ((- a') * d + c * b')
  lemma = solve p-2 6 (λ a b a' b' c d →
            (((⊝ (a ⊕ a')) ⊗ d) ⊕ (c ⊗ (b ⊕ b'))) ,
            ((((⊝ a) ⊗ d) ⊕ (c ⊗ b)) ⊕ (((⊝ a') ⊗ d) ⊕ (c ⊗ b'))))
            (λ {_} {_} {_} {_} {_} {_} → Eq.refl)

sform1-+ʳ : (p q q' : Pauli1) → sform1 p (q +₁ q') ≡ sform1 p q + sform1 p q'
sform1-+ʳ (a , b) (c , d) (c' , d') = lemma a b c d c' d'
  where
  lemma : (a b c d c' d' : ℤ ₚ) →
          (- a) * (d + d') + (c + c') * b
            ≡ ((- a) * d + c * b) + ((- a) * d' + c' * b)
  lemma = solve p-2 6 (λ a b c d c' d' →
            (((⊝ a) ⊗ (d ⊕ d')) ⊕ ((c ⊕ c') ⊗ b)) ,
            ((((⊝ a) ⊗ d) ⊕ (c ⊗ b)) ⊕ (((⊝ a) ⊗ d') ⊕ (c' ⊗ b))))
            (λ {_} {_} {_} {_} {_} {_} → Eq.refl)

sform-+ˡ : (u u' v : Pauli n) → sform (u +ₚ u') v ≡ sform u v + sform u' v
sform-+ˡ []       []         []       = Eq.sym (+-identityʳ ₀)
sform-+ˡ (x ∷ xs) (x' ∷ xs') (y ∷ ys) = begin
  sform1 (x +₁ x') y + sform (xs +ₚ xs') ys
    ≡⟨ Eq.cong₂ _+_ (sform1-+ˡ x x' y) (sform-+ˡ xs xs' ys) ⟩
  (sform1 x y + sform1 x' y) + (sform xs ys + sform xs' ys)
    ≡⟨ swap4ₚ (sform1 x y) (sform1 x' y) (sform xs ys) (sform xs' ys) ⟩
  (sform1 x y + sform xs ys) + (sform1 x' y + sform xs' ys)   ∎
  where open Eq.≡-Reasoning

sform-+ʳ : (u v v' : Pauli n) → sform u (v +ₚ v') ≡ sform u v + sform u v'
sform-+ʳ []       []       []         = Eq.sym (+-identityʳ ₀)
sform-+ʳ (x ∷ xs) (y ∷ ys) (y' ∷ ys') = begin
  sform1 x (y +₁ y') + sform xs (ys +ₚ ys')
    ≡⟨ Eq.cong₂ _+_ (sform1-+ʳ x y y') (sform-+ʳ xs ys ys') ⟩
  (sform1 x y + sform1 x y') + (sform xs ys + sform xs ys')
    ≡⟨ swap4ₚ (sform1 x y) (sform1 x y') (sform xs ys) (sform xs ys') ⟩
  (sform1 x y + sform xs ys) + (sform1 x y' + sform xs ys')   ∎
  where open Eq.≡-Reasoning

-- The three basis probes, all by computation at p = 2.
sform1-pIʳ : (a b : ℤ ₚ) → sform1 (a , b) pI ≡ ₀
sform1-pIʳ ₀ ₀ = auto
sform1-pIʳ ₀ ₁ = auto
sform1-pIʳ ₁ ₀ = auto
sform1-pIʳ ₁ ₁ = auto

probe-Z : (a b : ℤ ₚ) → sform1 (a , b) pZ ≡ ₀ → a ≡ ₀
probe-Z ₀ ₀ e = auto
probe-Z ₀ ₁ e = auto
probe-Z ₁ ₀ ()
probe-Z ₁ ₁ ()

probe-X : (a b : ℤ ₚ) → sform1 (a , b) pX ≡ ₀ → b ≡ ₀
probe-X ₀ ₀ e = auto
probe-X ₁ ₀ e = auto
probe-X ₀ ₁ ()
probe-X ₁ ₁ ()

sform1-pIˡ : (c d : ℤ ₚ) → sform1 pI (c , d) ≡ ₀
sform1-pIˡ ₀ ₀ = auto
sform1-pIˡ ₀ ₁ = auto
sform1-pIˡ ₁ ₀ = auto
sform1-pIˡ ₁ ₁ = auto

sform-pIʳ : (u : Pauli n) → sform u (pIₙ {n}) ≡ ₀
sform-pIʳ []             = Eq.refl
sform-pIʳ ((a , b) ∷ us) =
  Eq.trans (Eq.cong₂ _+_ (sform1-pIʳ a b) (sform-pIʳ us)) (+-identityˡ ₀)

sform-pIˡ : (v : Pauli n) → sform (pIₙ {n}) v ≡ ₀
sform-pIˡ []             = Eq.refl
sform-pIˡ ((c , d) ∷ vs) =
  Eq.trans (Eq.cong₂ _+_ (sform1-pIˡ c d) (sform-pIˡ vs)) (+-identityˡ ₀)

-- Nondegeneracy: only the origin pairs trivially with everything.
sform-nondeg : (u : Pauli n) → ((v : Pauli n) → sform u v ≡ ₀) → u ≡ pIₙ
sform-nondeg []             h = Eq.refl
sform-nondeg ((a , b) ∷ us) h =
  Eq.cong₂ _∷_ (Eq.cong₂ _,_ (probe-Z a b (probe pZ)) (probe-X a b (probe pX)))
               (sform-nondeg us tail)
  where
  probe : (x : Pauli1) → sform1 (a , b) x ≡ ₀
  probe x = Eq.trans (Eq.sym (+-identityʳ (sform1 (a , b) x)))
              (Eq.trans (Eq.cong (sform1 (a , b) x +_) (Eq.sym (sform-pIʳ us)))
                        (h (x ∷ pIₙ)))
  tail : (v : Pauli _) → sform us v ≡ ₀
  tail v = Eq.trans (Eq.sym (+-identityˡ (sform us v)))
             (Eq.trans (Eq.cong (_+ sform us v) (Eq.sym (sform1-pIʳ a b)))
                       (h (pI ∷ v)))

------------------------------------------------------------------------
-- The Pauli kernel
--
-- Conjugation by the Pauli W(u) fixes every W(v) up to the sign
-- (−1)^(sform u v): symplectically trivial, phase ι ∘ sform u.

incl : Pauli n → Cliff n
incl {n} u = record { symp = εˢ ; phase = λ v → ι (sform u v) ; refines = prf }
  where
  open Eq.≡-Reasoning
  prf : IsRefinement {n} εˢ (λ v → ι (sform u v))
  prf v w = begin
    ι (sform u (v +ₚ w))
      ≡⟨ Eq.cong ι (sform-+ʳ u v w) ⟩
    ι (sform u v + sform u w)
      ≡⟨ ι-+ (sform u v) (sform u w) ⟩
    ι (sform u v) + ι (sform u w)
      ≡⟨ Eq.sym (+-identityʳ (ι (sform u v) + ι (sform u w))) ⟩
    (ι (sform u v) + ι (sform u w)) + ₀
      ≡⟨ Eq.cong ((ι (sform u v) + ι (sform u w)) +_) (Eq.sym (δ-ε v w)) ⟩
    (ι (sform u v) + ι (sform u w)) + δ εˢ v w   ∎

incl-∙ : (u u' : Pauli n) → incl (u +ₚ u') ≈ᵛ (incl u ∙ᵛ incl u')
incl-∙ u u' = (λ _ → Eq.refl) , λ v → begin
  ι (sform (u +ₚ u') v)             ≡⟨ Eq.cong ι (sform-+ˡ u u' v) ⟩
  ι (sform u v + sform u' v)        ≡⟨ ι-+ (sform u v) (sform u' v) ⟩
  ι (sform u v) + ι (sform u' v)    ≡⟨ +-comm (ι (sform u v)) (ι (sform u' v)) ⟩
  ι (sform u' v) + ι (sform u v)    ∎
  where open Eq.≡-Reasoning

incl-ε : incl (pIₙ {n}) ≈ᵛ εᵛ
incl-ε = (λ _ → Eq.refl) , λ v → Eq.cong ι (sform-pIˡ v)

incl-cong : {u u' : Pauli n} → u ≡ u' → incl u ≈ᵛ incl u'
incl-cong Eq.refl = (λ _ → Eq.refl) , (λ _ → Eq.refl)

------------------------------------------------------------------------
-- Exactness at the Pauli end: incl is injective

ι-injective : {x y : ℤ ₚ} → ι x ≡ ι y → x ≡ y
ι-injective {₀} {₀} e = auto
ι-injective {₁} {₁} e = auto
ι-injective {₀} {₁} ()
ι-injective {₁} {₀} ()

incl-injective : {u u' : Pauli n} → incl u ≈ᵛ incl u' → u ≡ u'
incl-injective {n} {u} {u'} (_ , f) = begin
  u                    ≡⟨ Eq.sym (+ₚ-identityʳ u) ⟩
  u +ₚ pIₙ             ≡⟨ Eq.cong (u +ₚ_) (Eq.sym (+ₚ-self u')) ⟩
  u +ₚ (u' +ₚ u')      ≡⟨ Eq.sym (+ₚ-assoc u u' u') ⟩
  (u +ₚ u') +ₚ u'      ≡⟨ Eq.cong (_+ₚ u') (sform-nondeg (u +ₚ u') zero-form) ⟩
  pIₙ +ₚ u'            ≡⟨ +ₚ-identityˡ u' ⟩
  u'                   ∎
  where
  open Eq.≡-Reasoning
  -- u and u' pair identically with everything, and x + x = ₀ at p = 2.
  zero-form : (v : Pauli n) → sform (u +ₚ u') v ≡ ₀
  zero-form v = begin
    sform (u +ₚ u') v          ≡⟨ sform-+ˡ u u' v ⟩
    sform u v + sform u' v     ≡⟨ Eq.cong (_+ sform u' v) (ι-injective (f v)) ⟩
    sform u' v + sform u' v    ≡⟨ Eq.cong (sform u' v +_) (Eq.sym (neg-id (sform u' v))) ⟩
    sform u' v + - sform u' v  ≡⟨ +-inverseʳ (sform u' v) ⟩
    ₀                          ∎

------------------------------------------------------------------------
-- Exactness in the middle: the kernel of proj is the Pauli group
--
-- A pair whose symplectic part is trivial has an additive, 2-torsion
-- phase function; halving it gives an additive g : V → ℤ/2, and
-- nondegeneracy of sform realises g as sform u — so the pair is incl u.

-- Halving on the 2-torsion part of ℤ/4.
π : Φ → ℤ ₚ
π ₀ = ₀
π ₁ = ₀
π ₂ = ₁
π ₃ = ₀

π-ι : (x : Φ) → x + x ≡ ₀ → ι (π x) ≡ x
π-ι ₀ e = auto
π-ι ₂ e = auto
π-ι ₁ ()
π-ι ₃ ()

Additive : (Pauli n → ℤ ₚ) → Set
Additive {n} g = (v w : Pauli n) → g (v +ₚ w) ≡ g v + g w

-- The dual vector of an additive functional: read its values off the
-- standard basis, wire by wire.
dual : (Pauli n → ℤ ₚ) → Pauli n
dual {₀}    g = []
dual {₁₊ n} g = (g (pZ ∷ pIₙ) , g (pX ∷ pIₙ)) ∷ dual (λ v → g (pI ∷ v))

-- The four head cases of dual-correct, all by computation at p = 2.
sf-00 : (A B : ℤ ₚ) → (- A) * ₀ + ₀ * B ≡ ₀
sf-00 ₀ ₀ = auto
sf-00 ₀ ₁ = auto
sf-00 ₁ ₀ = auto
sf-00 ₁ ₁ = auto

sf-10 : (A B : ℤ ₚ) → (- A) * ₀ + ₁ * B ≡ B
sf-10 ₀ ₀ = auto
sf-10 ₀ ₁ = auto
sf-10 ₁ ₀ = auto
sf-10 ₁ ₁ = auto

sf-01 : (A B : ℤ ₚ) → (- A) * ₁ + ₀ * B ≡ A
sf-01 ₀ ₀ = auto
sf-01 ₀ ₁ = auto
sf-01 ₁ ₀ = auto
sf-01 ₁ ₁ = auto

sf-11 : (A B : ℤ ₚ) → (- A) * ₁ + ₁ * B ≡ A + B
sf-11 ₀ ₀ = auto
sf-11 ₀ ₁ = auto
sf-11 ₁ ₀ = auto
sf-11 ₁ ₁ = auto

cancel-selfₚ : (x : ℤ ₚ) → x ≡ x + x → x ≡ ₀
cancel-selfₚ ₀ e = auto
cancel-selfₚ ₁ ()

-- An additive functional vanishes at the origin.
additive-pIₙ : (g : Pauli n → ℤ ₚ) → Additive g → g pIₙ ≡ ₀
additive-pIₙ {n} g ga = cancel-selfₚ (g pIₙ)
  (Eq.trans (Eq.cong g (Eq.sym (+ₚ-identityˡ (pIₙ {n})))) (ga pIₙ pIₙ))

-- Splitting off the leading wire.
cons-split : {n : ℕ} (x : Pauli1) (vs : Pauli n) →
             (x ∷ pIₙ) +ₚ (pI ∷ vs) ≡ x ∷ vs
cons-split x vs = Eq.cong₂ _∷_ (+₁-identityʳ x) (+ₚ-identityˡ vs)

dual-correct : (g : Pauli n → ℤ ₚ) → Additive g →
               (v : Pauli n) → sform (dual g) v ≡ g v
dual-correct {₀}    g ga []             = Eq.sym (additive-pIₙ g ga)
dual-correct {₁₊ n} g ga ((c , d) ∷ vs) = begin
  sform1 (A , B) (c , d) + sform (dual g') vs
    ≡⟨ Eq.cong₂ _+_ (head c d) (dual-correct g' ga' vs) ⟩
  g ((c , d) ∷ pIₙ) + g' vs
    ≡⟨ Eq.sym (ga ((c , d) ∷ pIₙ) (pI ∷ vs)) ⟩
  g (((c , d) ∷ pIₙ) +ₚ (pI ∷ vs))
    ≡⟨ Eq.cong g (cons-split (c , d) vs) ⟩
  g ((c , d) ∷ vs)   ∎
  where
  open Eq.≡-Reasoning
  A = g (pZ ∷ pIₙ) ; B = g (pX ∷ pIₙ)
  g' = λ v → g (pI ∷ v)

  ga' : Additive g'
  ga' v w = Eq.trans (Eq.cong g (Eq.cong₂ _∷_ (Eq.sym (+₁-identityʳ pI)) Eq.refl))
                     (ga (pI ∷ v) (pI ∷ w))

  -- The leading wire: the four basis values of g, by additivity.
  head : (c d : ℤ ₚ) → sform1 (A , B) (c , d) ≡ g ((c , d) ∷ pIₙ)
  head ₀ ₀ = Eq.trans (sf-00 A B) (Eq.sym (additive-pIₙ g ga))
  head ₁ ₀ = sf-10 A B
  head ₀ ₁ = sf-01 A B
  head ₁ ₁ = Eq.trans (sf-11 A B)
    (Eq.trans (+-comm A B)
      (Eq.trans (Eq.sym (ga (pX ∷ pIₙ) (pZ ∷ pIₙ)))
                (Eq.cong g (Eq.cong₂ _∷_ Eq.refl (+ₚ-identityˡ pIₙ)))))

------------------------------------------------------------------------
-- The kernel is exactly the image of incl

ker⊆im-incl : (X : Cliff n) → symp X ≈ˢ εˢ → Σ[ u ∈ Pauli n ] (incl u ≈ᵛ X)
ker⊆im-incl {n} X triv = dual g , ((λ v → Eq.sym (triv v)) , realises)
  where
  open Eq.≡-Reasoning
  φ = phase X

  -- With no twist left, the phase function is additive.
  φ-add : (v w : Pauli n) → φ (v +ₚ w) ≡ φ v + φ w
  φ-add v w = begin
    φ (v +ₚ w)                    ≡⟨ refines X v w ⟩
    (φ v + φ w) + δ (symp X) v w
      ≡⟨ Eq.cong ((φ v + φ w) +_)
           (Eq.trans (δ-cong {S = symp X} {T = εˢ} triv v w) (δ-ε v w)) ⟩
    (φ v + φ w) + ₀               ≡⟨ +-identityʳ (φ v + φ w) ⟩
    φ v + φ w                     ∎

  -- ... and 2-torsion, since v +ₚ v = pIₙ.
  φ-2 : (v : Pauli n) → φ v + φ v ≡ ₀
  φ-2 v = Eq.trans (Eq.sym (Eq.trans (Eq.cong φ (Eq.sym (+ₚ-self v))) (φ-add v v)))
                   (phase-ε X)

  g : Pauli n → ℤ ₚ
  g v = π (φ v)

  g-ι : (v : Pauli n) → ι (g v) ≡ φ v
  g-ι v = π-ι (φ v) (φ-2 v)

  g-add : Additive g
  g-add v w = ι-injective (begin
    ι (g (v +ₚ w))       ≡⟨ g-ι (v +ₚ w) ⟩
    φ (v +ₚ w)           ≡⟨ φ-add v w ⟩
    φ v + φ w            ≡⟨ Eq.cong₂ _+_ (Eq.sym (g-ι v)) (Eq.sym (g-ι w)) ⟩
    ι (g v) + ι (g w)    ≡⟨ Eq.sym (ι-+ (g v) (g w)) ⟩
    ι (g v + g w)        ∎)

  realises : (v : Pauli n) → ι (sform (dual g) v) ≡ φ v
  realises v = Eq.trans (Eq.cong ι (dual-correct g g-add v)) (g-ι v)

------------------------------------------------------------------------
-- Exactness at the symplectic end: every symplectic map is realised
--
-- Each generator is lifted by hand — the phase it attaches to X^a Z^b —
-- and words are lifted by the group multiplication.  Surjectivity of the
-- plain symplectic action (Symplectic.Surjectivity) then finishes the job.

-- The quarter turn: the phase gate sends X to i X Z, so its phase
-- function leaves the 2-torsion part of ℤ/4.  (Not a homomorphism — that
-- is exactly the p = 2 anomaly.)
inc : ℤ ₚ → Φ
inc ₀ = ₀
inc ₁ = ₁

------------------------------------------------------------------------
-- Peeling wires off the cocycle

γ-cons : (a b c d : ℤ ₚ) (vs ws : Pauli n) →
         γ ((a , b) ∷ vs) ((c , d) ∷ ws) ≡ ι (b * c) + γ vs ws
γ-cons a b c d vs ws = ι-+ (b * c) (β vs ws)

γ-cons2 : (a b a' b' c d c' d' : ℤ ₚ) (vs ws : Pauli n) →
          γ ((a , b) ∷ (a' , b') ∷ vs) ((c , d) ∷ (c' , d') ∷ ws)
            ≡ ι (b * c) + (ι (b' * c') + γ vs ws)
γ-cons2 a b a' b' c d c' d' vs ws =
  Eq.trans (γ-cons a b c d ((a' , b') ∷ vs) ((c' , d') ∷ ws))
           (Eq.cong (ι (b * c) +_) (γ-cons a' b' c' d' vs ws))

-- The untouched wires contribute the same cocycle to both halves of a
-- twist, and cancel.
head-cancel : (x p q : Φ) → x + x ≡ ₀ → (x + p) + (x + q) ≡ p + q
head-cancel x p q hx = Eq.trans (swap4 x p x q)
  (Eq.trans (Eq.cong (_+ (p + q)) hx) (+-identityˡ (p + q)))

tail-cancel : (x y : Φ) (vs ws : Pauli n) →
              (x + γ vs ws) + (y + γ vs ws) ≡ x + y
tail-cancel x y vs ws = Eq.trans (swap4 x (γ vs ws) y (γ vs ws))
  (Eq.trans (Eq.cong ((x + y) +_) (γ-2 vs ws)) (+-identityʳ (x + y)))

shuffle-2 : (x x' g y y' : Φ) →
            (x + (x' + g)) + (y + (y' + g)) ≡ ((x + x') + (y + y')) + (g + g)
shuffle-2 = solve 2 5 (λ x x' g y y' →
              ((x ⊕ (x' ⊕ g)) ⊕ (y ⊕ (y' ⊕ g))) ,
              (((x ⊕ x') ⊕ (y ⊕ y')) ⊕ (g ⊕ g)))
              (λ {_} {_} {_} {_} {_} → Eq.refl)

tail-cancel2 : (x x' y y' : Φ) (vs ws : Pauli n) →
               (x + (x' + γ vs ws)) + (y + (y' + γ vs ws)) ≡ (x + x') + (y + y')
tail-cancel2 x x' y y' vs ws = Eq.trans (shuffle-2 x x' (γ vs ws) y y')
  (Eq.trans (Eq.cong (((x + x') + (y + y')) +_) (γ-2 vs ws))
            (+-identityʳ ((x + x') + (y + y'))))

------------------------------------------------------------------------
-- The twist of each generator

δ-H : (a b c d : ℤ ₚ) (vs ws : Pauli n) →
      δ ⟦ gate₁ H-gate ⟧ᵍ ((a , b) ∷ vs) ((c , d) ∷ ws) ≡ ι (a * (- d)) + ι (b * c)
δ-H a b c d vs ws = begin
  γ ((- b , a) ∷ vs) ((- d , c) ∷ ws) + γ ((a , b) ∷ vs) ((c , d) ∷ ws)
    ≡⟨ Eq.cong₂ _+_ (γ-cons (- b) a (- d) c vs ws) (γ-cons a b c d vs ws) ⟩
  (ι (a * (- d)) + γ vs ws) + (ι (b * c) + γ vs ws)
    ≡⟨ tail-cancel (ι (a * (- d))) (ι (b * c)) vs ws ⟩
  ι (a * (- d)) + ι (b * c)   ∎
  where open Eq.≡-Reasoning

δ-S : (a b c d : ℤ ₚ) (vs ws : Pauli n) →
      δ ⟦ gate₁ S-gate ⟧ᵍ ((a , b) ∷ vs) ((c , d) ∷ ws) ≡ ι ((b + a) * c) + ι (b * c)
δ-S a b c d vs ws = begin
  γ ((a , b + a) ∷ vs) ((c , d + c) ∷ ws) + γ ((a , b) ∷ vs) ((c , d) ∷ ws)
    ≡⟨ Eq.cong₂ _+_ (γ-cons a (b + a) c (d + c) vs ws) (γ-cons a b c d vs ws) ⟩
  (ι ((b + a) * c) + γ vs ws) + (ι (b * c) + γ vs ws)
    ≡⟨ tail-cancel (ι ((b + a) * c)) (ι (b * c)) vs ws ⟩
  ι ((b + a) * c) + ι (b * c)   ∎
  where open Eq.≡-Reasoning

δ-CZ : (a b a' b' c d c' d' : ℤ ₚ) (vs ws : Pauli n) →
       δ ⟦ gate₂ CZ-gate ⟧ᵍ ((a , b) ∷ (a' , b') ∷ vs) ((c , d) ∷ (c' , d') ∷ ws)
         ≡ (ι ((b + a') * c) + ι ((b' + a) * c')) + (ι (b * c) + ι (b' * c'))
δ-CZ a b a' b' c d c' d' vs ws = begin
  γ ((a , b + a') ∷ (a' , b' + a) ∷ vs) ((c , d + c') ∷ (c' , d' + c) ∷ ws)
    + γ ((a , b) ∷ (a' , b') ∷ vs) ((c , d) ∷ (c' , d') ∷ ws)
    ≡⟨ Eq.cong₂ _+_ (γ-cons2 a (b + a') a' (b' + a) c (d + c') c' (d' + c) vs ws)
                    (γ-cons2 a b a' b' c d c' d' vs ws) ⟩
  (ι ((b + a') * c) + (ι ((b' + a) * c') + γ vs ws))
    + (ι (b * c) + (ι (b' * c') + γ vs ws))
    ≡⟨ tail-cancel2 (ι ((b + a') * c)) (ι ((b' + a) * c'))
                    (ι (b * c)) (ι (b' * c')) vs ws ⟩
  (ι ((b + a') * c) + ι ((b' + a) * c')) + (ι (b * c) + ι (b' * c'))   ∎
  where open Eq.≡-Reasoning

δ-↥ : (g : Gen n) (a b c d : ℤ ₚ) (vs ws : Pauli n) →
      δ ⟦ g ↥ ⟧ᵍ ((a , b) ∷ vs) ((c , d) ∷ ws) ≡ δ ⟦ g ⟧ᵍ vs ws
δ-↥ g a b c d vs ws = begin
  γ ((a , b) ∷ actg g vs) ((c , d) ∷ actg g ws) + γ ((a , b) ∷ vs) ((c , d) ∷ ws)
    ≡⟨ Eq.cong₂ _+_ (γ-cons a b c d (actg g vs) (actg g ws)) (γ-cons a b c d vs ws) ⟩
  (ι (b * c) + γ (actg g vs) (actg g ws)) + (ι (b * c) + γ vs ws)
    ≡⟨ head-cancel (ι (b * c)) (γ (actg g vs) (actg g ws)) (γ vs ws) (ι-2 (b * c)) ⟩
  γ (actg g vs) (actg g ws) + γ vs ws   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The head identities: each generator's phase refines its twist
--
-- H and S are small enough to check by computation; CZ has six free
-- scalars, so it goes through ι-additivity and one ℤ/2 identity.

head-H : (a b c d : ℤ ₚ) →
         ι ((a + c) * (b + d))
           ≡ (ι (a * b) + ι (c * d)) + (ι (a * (- d)) + ι (b * c))
head-H ₀ ₀ ₀ ₀ = auto
head-H ₀ ₀ ₀ ₁ = auto
head-H ₀ ₀ ₁ ₀ = auto
head-H ₀ ₀ ₁ ₁ = auto
head-H ₀ ₁ ₀ ₀ = auto
head-H ₀ ₁ ₀ ₁ = auto
head-H ₀ ₁ ₁ ₀ = auto
head-H ₀ ₁ ₁ ₁ = auto
head-H ₁ ₀ ₀ ₀ = auto
head-H ₁ ₀ ₀ ₁ = auto
head-H ₁ ₀ ₁ ₀ = auto
head-H ₁ ₀ ₁ ₁ = auto
head-H ₁ ₁ ₀ ₀ = auto
head-H ₁ ₁ ₀ ₁ = auto
head-H ₁ ₁ ₁ ₀ = auto
head-H ₁ ₁ ₁ ₁ = auto

head-S : (a b c : ℤ ₚ) →
         inc (a + c) ≡ (inc a + inc c) + (ι ((b + a) * c) + ι (b * c))
head-S ₀ ₀ ₀ = auto
head-S ₀ ₀ ₁ = auto
head-S ₀ ₁ ₀ = auto
head-S ₀ ₁ ₁ = auto
head-S ₁ ₀ ₀ = auto
head-S ₁ ₀ ₁ = auto
head-S ₁ ₁ ₀ = auto
head-S ₁ ₁ ₁ = auto

-- The CZ identity in ℤ/2: the b's cancel in characteristic 2, leaving
-- the polarisation of the product a·a'.
cz-ℤ : (a b a' b' c c' : ℤ ₚ) →
       (a + c) * (a' + c')
         ≡ (a * a' + c * c')
           + (((b + a') * c + (b' + a) * c') + (b * c + b' * c'))
cz-ℤ = solve p-2 6 (λ a b a' b' c c' →
         ((a ⊕ c) ⊗ (a' ⊕ c')) ,
         ((a ⊗ a' ⊕ c ⊗ c')
           ⊕ ((((b ⊕ a') ⊗ c) ⊕ ((b' ⊕ a) ⊗ c')) ⊕ ((b ⊗ c) ⊕ (b' ⊗ c')))))
         (λ {_} {_} {_} {_} {_} {_} → Eq.refl)

head-CZ : (a b a' b' c c' : ℤ ₚ) →
          ι ((a + c) * (a' + c'))
            ≡ (ι (a * a') + ι (c * c'))
              + ((ι ((b + a') * c) + ι ((b' + a) * c')) + (ι (b * c) + ι (b' * c')))
head-CZ a b a' b' c c' = begin
  ι ((a + c) * (a' + c'))
    ≡⟨ Eq.cong ι (cz-ℤ a b a' b' c c') ⟩
  ι ((a * a' + c * c') + (((b + a') * c + (b' + a) * c') + (b * c + b' * c')))
    ≡⟨ ι-+ (a * a' + c * c')
           (((b + a') * c + (b' + a) * c') + (b * c + b' * c')) ⟩
  ι (a * a' + c * c') + ι (((b + a') * c + (b' + a) * c') + (b * c + b' * c'))
    ≡⟨ Eq.cong₂ _+_ (ι-+ (a * a') (c * c'))
         (Eq.trans (ι-+ ((b + a') * c + (b' + a) * c') (b * c + b' * c'))
                   (Eq.cong₂ _+_ (ι-+ ((b + a') * c) ((b' + a) * c'))
                                 (ι-+ (b * c) (b' * c')))) ⟩
  (ι (a * a') + ι (c * c'))
    + ((ι ((b + a') * c) + ι ((b' + a) * c')) + (ι (b * c) + ι (b' * c')))   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The generators as elements of the group

φᵍ : (g : Gen n) → Pauli n → Φ
φᵍ (gate₁ H-gate)  ((a , b) ∷ vs)             = ι (a * b)
φᵍ (gate₁ S-gate)  ((a , b) ∷ vs)             = inc a
φᵍ (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ vs) = ι (a * a')
φᵍ (g ↥)           (x ∷ vs)                   = φᵍ g vs

refines-g : (g : Gen n) → IsRefinement ⟦ g ⟧ᵍ (φᵍ g)
refines-g (gate₁ H-gate) ((a , b) ∷ vs) ((c , d) ∷ ws) = begin
  ι ((a + c) * (b + d))
    ≡⟨ head-H a b c d ⟩
  (ι (a * b) + ι (c * d)) + (ι (a * (- d)) + ι (b * c))
    ≡⟨ Eq.cong ((ι (a * b) + ι (c * d)) +_) (Eq.sym (δ-H a b c d vs ws)) ⟩
  (ι (a * b) + ι (c * d))
    + δ ⟦ gate₁ H-gate ⟧ᵍ ((a , b) ∷ vs) ((c , d) ∷ ws)   ∎
  where open Eq.≡-Reasoning
refines-g (gate₁ S-gate) ((a , b) ∷ vs) ((c , d) ∷ ws) = begin
  inc (a + c)
    ≡⟨ head-S a b c ⟩
  (inc a + inc c) + (ι ((b + a) * c) + ι (b * c))
    ≡⟨ Eq.cong ((inc a + inc c) +_) (Eq.sym (δ-S a b c d vs ws)) ⟩
  (inc a + inc c)
    + δ ⟦ gate₁ S-gate ⟧ᵍ ((a , b) ∷ vs) ((c , d) ∷ ws)   ∎
  where open Eq.≡-Reasoning
refines-g (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ vs) ((c , d) ∷ (c' , d') ∷ ws) = begin
  ι ((a + c) * (a' + c'))
    ≡⟨ head-CZ a b a' b' c c' ⟩
  (ι (a * a') + ι (c * c'))
    + ((ι ((b + a') * c) + ι ((b' + a) * c')) + (ι (b * c) + ι (b' * c')))
    ≡⟨ Eq.cong ((ι (a * a') + ι (c * c')) +_)
               (Eq.sym (δ-CZ a b a' b' c d c' d' vs ws)) ⟩
  (ι (a * a') + ι (c * c'))
    + δ ⟦ gate₂ CZ-gate ⟧ᵍ ((a , b) ∷ (a' , b') ∷ vs) ((c , d) ∷ (c' , d') ∷ ws)   ∎
  where open Eq.≡-Reasoning
refines-g (g ↥) ((a , b) ∷ vs) ((c , d) ∷ ws) = begin
  φᵍ g (vs +ₚ ws)
    ≡⟨ refines-g g vs ws ⟩
  (φᵍ g vs + φᵍ g ws) + δ ⟦ g ⟧ᵍ vs ws
    ≡⟨ Eq.cong ((φᵍ g vs + φᵍ g ws) +_) (Eq.sym (δ-↥ g a b c d vs ws)) ⟩
  (φᵍ g vs + φᵍ g ws) + δ ⟦ g ↥ ⟧ᵍ ((a , b) ∷ vs) ((c , d) ∷ ws)   ∎
  where open Eq.≡-Reasoning

cliffᵍ : Gen n → Cliff n
cliffᵍ g = record { symp = ⟦ g ⟧ᵍ ; phase = φᵍ g ; refines = refines-g g }

-- A circuit denotes the product of its generators.
⟦_⟧ᵛ : Circuit n → Cliff n
⟦ [ g ]ʷ ⟧ᵛ = cliffᵍ g
⟦ ε ⟧ᵛ      = εᵛ
⟦ w • v ⟧ᵛ  = ⟦ w ⟧ᵛ ∙ᵛ ⟦ v ⟧ᵛ

-- ... over the symplectic map it already denoted.
symp-⟦⟧ᵛ : (w : Circuit n) → symp ⟦ w ⟧ᵛ ≈ˢ ⟦ w ⟧
symp-⟦⟧ᵛ [ g ]ʷ  x = Eq.refl
symp-⟦⟧ᵛ ε       x = Eq.refl
symp-⟦⟧ᵛ (w • v) x =
  Eq.trans (Eq.cong (ap (symp ⟦ w ⟧ᵛ)) (symp-⟦⟧ᵛ v x)) (symp-⟦⟧ᵛ w (ap ⟦ v ⟧ x))

-- Every symplectic map lifts: a Clifford circuit realises it, and its
-- phase function comes along for the ride.
proj-surjective : (S : Symplectic n) → Σ[ X ∈ Cliff n ] (symp X ≈ˢ S)
proj-surjective S with surj-nf S
... | w , e = ⟦ w ⟧ᵛ , λ x → Eq.trans (symp-⟦⟧ᵛ w x) (e x)

------------------------------------------------------------------------
-- The extension
--
--     1 ─→ Pauli n ─→ VSp n ─→ Sp(2n,2) ─→ 1
--
-- Nothing above provides a section of proj: a section would be a choice
-- of phase function φ_S, one for each symplectic S, with
-- φ_(S T) = φ_T + φ_S ∘ T.  The obvious candidate φ ≡ 0 is admissible
-- only for the S that preserve the cocycle γ outright — an orthogonal
-- subgroup of Sp, not all of it.  That is where the non-splitness of the
-- qubit Clifford group lives, and the contrast with odd p, where the
-- projective Clifford group really is Pauli n ⋊ Sp(2n,p).

module _ (n : ℕ) where

  private
    module MN = MonoidMorphisms (Group.rawMonoid (+ₚ-group n))
                                (Group.rawMonoid (VSp-group n))
    module MP = MonoidMorphisms (Group.rawMonoid (VSp-group n))
                                (Group.rawMonoid (Sp-group n))

  incl-isMonoidHomomorphism : MN.IsMonoidHomomorphism incl
  incl-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = incl-cong }
      ; homo              = incl-∙
      }
    ; ε-homo = incl-ε
    }

  proj-isMonoidHomomorphism : MP.IsMonoidHomomorphism symp
  proj-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = proj₁ }
      ; homo              = λ _ _ _ → Eq.refl
      }
    ; ε-homo = λ _ → Eq.refl
    }

  VSp-extension : Extension (+ₚ-group n) (Sp-group n)
  VSp-extension = record
    { total           = VSp-group n
    ; incl            = incl
    ; proj            = symp
    ; incl-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          (+ₚ-group n) (VSp-group n) incl-isMonoidHomomorphism
    ; proj-homo       = isMonoidHomomorphism⇒isGroupHomomorphism
                          (VSp-group n) (Sp-group n) proj-isMonoidHomomorphism
    ; incl-injective  = incl-injective
    ; proj-surjective = proj-surjective
    ; proj-kills-incl = λ _ _ → Eq.refl
    ; ker⊆im-incl     = ker⊆im-incl
    }
