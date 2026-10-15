------------------------------------------------------------------------
-- Presentations of groups
--
-- A NaturalP derivation on k wires holds on the bottom k wires of every
-- wider circuit.
--
-- Every rule of NaturalP, the swap rules included, is stated on the
-- bottom wires for every width above its own, and widening a circuit
-- (`_↓ᵏ_`, idle wires on top) leaves its gates where they are.  So an
-- axiom instance widens to an instance of the same axiom, and a
-- derivation to a derivation (`widen`); with completeness on k wires
-- (`padded`), two k-wire circuits with the same matrix are equal on the
-- bottom k wires of any circuit.  Circuit.Prop's pad does this for
-- k ≤ 4 through the symmetry; here it is direct and for every k.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Pad where

open import Data.Nat.Base using (ℕ ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Syntactics
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

private
  variable
    k m : ℕ

-- Idle wires on top commute with an idle wire below.
↑↓ : ∀ {k} (w : Circuit k) (m : ℕ) → (w ↑) ↓ᵏ m ≡ (w ↓ᵏ m) ↑
↑↓ [ g ]ʷ  m = Eq.refl
↑↓ ε       m = Eq.refl
↑↓ (u • v) m = Eq.cong₂ _•_ (↑↓ u m) (↑↓ v m)

widen-axiom : ∀ {k} (m : ℕ) {w v : Circuit k} → k VRel, w === v →
              (k + m) VRel, w ↓ᵏ m === v ↓ᵏ m
widen-axiom m (srel (σrel σ-inv))          = srel (σrel σ-inv)
widen-axiom m (srel (σrel (σ-nat₁ h)))     = srel (σrel (σ-nat₁ h))
widen-axiom m (srel (σrel (σ-nat₂ h)))     = srel (σrel (σ-nat₂ h))
widen-axiom m (srel (σrel (σ-nat₃ h)))     = srel (σrel (σ-nat₃ h))
widen-axiom m (srel (srel X²))         = srel (srel X²)
widen-axiom m (srel (srel CX²))        = srel (srel CX²)
widen-axiom m (srel (srel CCX²))       = srel (srel CCX²)
widen-axiom m (srel (srel HH²))        = srel (srel HH²)
widen-axiom m (srel (srel sw-def))     = srel (srel sw-def)
widen-axiom m (srel (srel X-control))  = srel (srel X-control)
widen-axiom m (srel (srel X-controlᵣ)) = srel (srel X-controlᵣ)
widen-axiom m (srel (srel CNOT-S3))    = srel (srel CNOT-S3)
widen-axiom m (srel (srel X-Z))        = srel (srel X-Z)
widen-axiom m (srel (srel CCX-sym))    = srel (srel CCX-sym)
widen-axiom m (srel (srel CCX-neg))    = srel (srel CCX-neg)
widen-axiom m (srel (srel CCX-XC))     = srel (srel CCX-XC)
widen-axiom m (srel (srel HH-swap₀))   = srel (srel HH-swap₀)
widen-axiom m (srel (srel HH-swap₁))   = srel (srel HH-swap₁)
widen-axiom m (srel (srel CCX-HH))     = srel (srel CCX-HH)
widen-axiom m (srel (srel CCX-comm))   = srel (srel CCX-comm)
widen-axiom m (cong↑ {w = w} {v = v} x) =
  Eq.subst₂ (_VRel,_===_ _) (Eq.sym (↑↓ w m)) (Eq.sym (↑↓ v m))
    (cong↑ (widen-axiom m x))
widen-axiom m (comm₁ h g) = comm₁ h (g ↧ᵏ m)
widen-axiom m (comm₂ h g) = comm₂ h (g ↧ᵏ m)
widen-axiom m (comm₃ h g) = comm₃ h (g ↧ᵏ m)
widen-axiom m (ω↑=ω ())

widen : ∀ {k} (m : ℕ) {w v : Circuit k} → k ⊢ w ≈ v → (k + m) ⊢ w ↓ᵏ m ≈ v ↓ᵏ m
widen m PB.refl        = PB.refl
widen m (PB.sym p)     = PB.sym (widen m p)
widen m (PB.trans p q) = PB.trans (widen m p) (widen m q)
widen m (PB.cong p q)  = PB.cong (widen m p) (widen m q)
widen m PB.assoc       = PB.assoc
widen m PB.left-unit   = PB.left-unit
widen m PB.right-unit  = PB.right-unit
widen m (PB.axiom x)   = PB.axiom (widen-axiom m x)

-- Completeness on k wires, on the bottom k wires of any circuit.
padded : ∀ {k} → (∀ {u v : Circuit k} → interpret u ≡ interpret v → k ⊢ u ≈ v) →
         (m : ℕ) {u v : Circuit k} → interpret u ≡ interpret v → (k + m) ⊢ u ↓ᵏ m ≈ v ↓ᵏ m
padded complete m {u} {v} e = widen m (complete {u} {v} e)
