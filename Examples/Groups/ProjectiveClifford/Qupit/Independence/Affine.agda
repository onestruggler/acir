------------------------------------------------------------------------
-- Presentations of groups
--
-- The affine symplectic model of the qupit Clifford rules, with a
-- twisted CZ
--
-- Modulo scalars, a Clifford circuit on n qupits is an affine
-- symplectic map of F_p^{2n}: a symplectic matrix, the action on the
-- Paulis, together with a translation recording the signs.  This
-- module builds that model of Paper-V1's alphabet at widths ≤ 2, with
-- an optional twist of CZ, and the decision procedure that checks a
-- relation in it by evaluating both sides at every point.
--
-- A point of width 1 is a pair ⟨ x , z ⟩, of width 2 two of those,
-- a ∣ b, wire 0 first.  An element is a map of points, and a word acts
-- left to right: w • v is w, then v.  The generators, as in the
-- survey's true_asp (local/paper-v1-minimality/verify_witnesses.py),
-- are
--
--   H   ⟨ x , z ⟩ ↦ ⟨ z , −x ⟩
--   S   ⟨ x , z ⟩ ↦ ⟨ x + z + c , z ⟩
--   CZ  ⟨ x₀ , z₀ ⟩ ∣ ⟨ x₁ , z₁ ⟩ ↦ ⟨ x₀ + z₁ + t , z₀ ⟩ ∣ ⟨ x₁ + z₀ + t , z₁ ⟩
--
-- where c is −½ and t is the twist: CZ followed by the Pauli
-- (Z ⊗ Z)^t.  At t = 0 this is the affine symplectic group itself, and
-- every rule holds; at t ≠ 0 exactly semi-M↑CZ fails.  The survey
-- checked both numerically at p = 3, 5, 7, 11; SemiMCZ3 and SemiMCZ5
-- prove the second at p = 3 and p = 5.
--
-- Maps of points under composition are a monoid on the nose, with
-- equality pointwise, so associativity and the unit laws hold by refl
-- and the structural rules hold by refl too: generators on disjoint
-- wires act on disjoint coordinates.  Widths ≥ 3 are not modelled:
-- their points are the one-point set, so every relation holds there.
-- An instance at width ≤ 2 only needs the model up to width 2.
--
-- Two choices keep the evaluation cheap.  The constant c is a
-- parameter, a numeral, rather than −½ spelled through Paper-V1's ½:
-- Agda does not memoise a definition, and ½ is a Bézout computation,
-- which every S letter at every point would otherwise redo.  And
-- points are data rather than Σ-pairs, with every generator forcing
-- the coordinates it reads, so that the image of a point is evaluated
-- once rather than once per projection.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Independence.Affine
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  (c t : ℤ ₚ)
  where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_ ; all?)
open import Data.Unit using (⊤)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong ; cong₂)
open import Relation.Nullary.Decidable
  using (Dec ; yes ; map′ ; _×?_ ; True ; False ; toWitness ; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen as Pap
open Pap using
  (SympGate ; H-gate ; S-gate ; CZ-gate ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Maps of a set, composed left to right, equal pointwise

End : Set → Monoid 0ℓ 0ℓ
End A = record
  { Carrier  = A → A
  ; _≈_      = λ f g → ∀ x → f x ≡ g x
  ; _∙_      = λ f g x → g (f x)
  ; ε        = λ x → x
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl  = λ _ → refl
          ; sym   = λ e x → sym (e x)
          ; trans = λ e e' x → trans (e x) (e' x) }
        ; ∙-cong = λ {f} {f'} {g} {g'} e e' x →
                     trans (cong g (e x)) (e' (f' x)) }
      ; assoc = λ _ _ _ _ → refl }
    ; identity = (λ _ _ → refl) , (λ _ _ → refl) } }

------------------------------------------------------------------------
-- Points

F : Set
F = ℤ ₚ

-- The coordinates ⟨ x , z ⟩ of one wire, and of two wires.
data Wire : Set where
  ⟨_,_⟩ : F → F → Wire

infix 5 _∣_
data Wires : Set where
  _∣_ : Wire → Wire → Wires

Pt : ℕ → Set
Pt 0      = ⊤
Pt 1      = Wire
Pt 2      = Wires
Pt (₃₊ _) = ⊤

mon : ℕ → Monoid 0ℓ 0ℓ
mon n = End (Pt n)

-- force x k evaluates the coordinate x to a numeral before handing it
-- to k, which may then use it any number of times.
force : ∀ {m} {A : Set} → Fin m → (Fin m → A) → A
force zero    k = k zero
force (suc i) k = force i (λ j → k (suc j))

------------------------------------------------------------------------
-- The generators

h₁ : Wire → Wire
h₁ ⟨ x , z ⟩ = force x λ x → force z λ z → ⟨ z , - x ⟩

s₁ : Wire → Wire
s₁ ⟨ x , z ⟩ = force x λ x → force z λ z → ⟨ (x + z) + c , z ⟩

cz₂ : Wires → Wires
cz₂ (⟨ x₀ , z₀ ⟩ ∣ ⟨ x₁ , z₁ ⟩) =
  force x₀ λ x₀ → force z₀ λ z₀ → force x₁ λ x₁ → force z₁ λ z₁ →
  ⟨ (x₀ + z₁) + t , z₀ ⟩ ∣ ⟨ (x₁ + z₀) + t , z₁ ⟩

one : SympGate 1 → Wire → Wire
one H-gate = h₁
one S-gate = s₁

two : SympGate 2 → Wires → Wires
two CZ-gate = cz₂

-- A one-wire map on wire 0, and a two-wire map on wires 0 and 1.
on₀ : ∀ n → (Wire → Wire) → Pt n → Pt n
on₀ 0      _ x       = x
on₀ 1      f x       = f x
on₀ 2      f (a ∣ b) = f a ∣ b
on₀ (₃₊ _) _ x       = x

on₀₁ : ∀ n → (Wires → Wires) → Pt n → Pt n
on₀₁ 0      _ x = x
on₀₁ 1      _ x = x
on₀₁ 2      f x = f x
on₀₁ (₃₊ _) _ x = x

-- The shift: a map of width n acts on the wires above wire 0.
σ : (Pt n → Pt n) → Pt (suc n) → Pt (suc n)
σ {0}      _ x       = x
σ {1}      f (a ∣ b) = a ∣ f b
σ {2}      _ x       = x
σ {₃₊ _}   _ x       = x

⟦_⟧₀ : Gen n → Pt n → Pt n
⟦ gate₀ () ⟧₀
⟦_⟧₀ {n} (gate₁ h) = on₀ n (one h)
⟦_⟧₀ {n} (gate₂ h) = on₀₁ n (two h)
⟦ g ↥ ⟧₀           = σ ⟦ g ⟧₀

------------------------------------------------------------------------
-- The shift is a homomorphism, and the structural rules hold

σ-hom : MonoidMorphisms.IsMonoidHomomorphism
          (Monoid.rawMonoid (mon n)) (Monoid.rawMonoid (mon (suc n))) (σ {n})
σ-hom {n} = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = σ-cong n }
      ; homo = λ _ _ → σ-homo n }
  ; ε-homo = σ-ε n }
  where
  σ-cong : ∀ n {f g : Pt n → Pt n} → (∀ x → f x ≡ g x) →
           ∀ x → σ f x ≡ σ g x
  σ-cong 0      _ _       = refl
  σ-cong 1      e (a ∣ b) = cong (a ∣_) (e b)
  σ-cong 2      _ _       = refl
  σ-cong (₃₊ _) _ _       = refl

  σ-homo : ∀ n {f g : Pt n → Pt n} → ∀ x → σ (λ y → g (f y)) x ≡ σ g (σ f x)
  σ-homo 0      _       = refl
  σ-homo 1      (_ ∣ _) = refl
  σ-homo 2      _       = refl
  σ-homo (₃₊ _) _       = refl

  σ-ε : ∀ n → ∀ x → σ {n} (λ y → y) x ≡ x
  σ-ε 0      _       = refl
  σ-ε 1      (_ ∣ _) = refl
  σ-ε 2      _       = refl
  σ-ε (₃₊ _) _       = refl

-- comm₁: a map shifted up a wire and a map on wire 0 act on disjoint
-- coordinates.  Below width 2 there is no shifted generator.
comm₁ : ∀ n (h : SympGate 1) (g : Gen n) →
        ∀ x → ⟦ gate₁ h ⟧₀ (⟦ g ↥ ⟧₀ x) ≡ ⟦ g ↥ ⟧₀ (⟦ gate₁ h ⟧₀ x)
comm₁ 0      _ (gate₀ ()) _
comm₁ 1      _ _          (_ ∣ _) = refl
comm₁ (₂₊ _) _ _          _       = refl

-- comm₂: below width 3 there is no twice-shifted generator, and from
-- width 3 there is nothing to check.
comm₂ : ∀ n (h : SympGate 2) (g : Gen n) →
        ∀ x → ⟦ gate₂ h ⟧₀ (⟦ g ↥ ↥ ⟧₀ x) ≡ ⟦ g ↥ ↥ ⟧₀ (⟦ gate₂ h ⟧₀ x)
comm₂ 0       _ (gate₀ ()) _
comm₂ (suc _) _ _          _ = refl

------------------------------------------------------------------------
-- Deciding a relation by evaluation at every point

private
  _≟₁_ : (a b : Wire) → Dec (a ≡ b)
  ⟨ x , z ⟩ ≟₁ ⟨ x' , z' ⟩ =
    map′ (λ (e , e') → cong₂ ⟨_,_⟩ e e') (λ { refl → refl , refl })
      ((x ≟ x') ×? (z ≟ z'))

  _≟₂_ : (a b : Wires) → Dec (a ≡ b)
  (a ∣ b) ≟₂ (a' ∣ b') =
    map′ (λ (e , e') → cong₂ _∣_ e e') (λ { refl → refl , refl })
      ((a ≟₁ a') ×? (b ≟₁ b'))

≈-dec : ∀ n (f g : Pt n → Pt n) → Dec (∀ x → f x ≡ g x)
≈-dec 0      f g = yes λ _ → refl
≈-dec 1      f g =
  map′ (λ { e ⟨ x , z ⟩ → e x z }) (λ e x z → e ⟨ x , z ⟩)
    (all? λ x → all? λ z → f ⟨ x , z ⟩ ≟₁ g ⟨ x , z ⟩)
≈-dec 2      f g =
  map′ (λ { e (⟨ x₀ , z₀ ⟩ ∣ ⟨ x₁ , z₁ ⟩) → e x₀ z₀ x₁ z₁ })
       (λ e x₀ z₀ x₁ z₁ → e (⟨ x₀ , z₀ ⟩ ∣ ⟨ x₁ , z₁ ⟩))
    (all? λ x₀ → all? λ z₀ → all? λ x₁ → all? λ z₁ →
       f (⟨ x₀ , z₀ ⟩ ∣ ⟨ x₁ , z₁ ⟩) ≟₂ g (⟨ x₀ , z₀ ⟩ ∣ ⟨ x₁ , z₁ ⟩))
≈-dec (₃₊ _) f g = yes λ _ → refl

-- A relation that evaluates to true holds; one that evaluates to
-- false fails.
decide : ∀ n {f g : Pt n → Pt n} → True (≈-dec n f g) → ∀ x → f x ≡ g x
decide n = toWitness

refute : ∀ n {f g : Pt n → Pt n} → False (≈-dec n f g) →
         ¬ (∀ x → f x ≡ g x)
refute n = toWitnessFalse
