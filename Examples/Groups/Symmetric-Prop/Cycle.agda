------------------------------------------------------------------------
-- Presentations of groups
--
-- An idle wire at the bottom or on top, in any PROP, at every width.
--
-- The cycle of swaps that carries wire 0 to the top and every other
-- wire one down (`cyc`) carries a circuit shifted one wire up to the
-- same circuit with an idle wire on top (`nat`): the swap rules say so
-- for one gate, hence for a circuit.  Circuit.Prop states naturality
-- for the cycle σ[ k ] at numerals k ≤ 4 only, its width ₁₊ k + n
-- meeting the circuit's only there; this cycle is indexed by the
-- circuit's own width.  The argument is Real-Clifford+CH.TopWeakening's,
-- for any family with a designated swap.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)
import Circuit.Base

module Examples.Groups.Symmetric-Prop.Cycle
  (Gate : ℕ → Set) (Ex-gate : Gate 2)
  (_SRel,_===_ : (n : ℕ) → Circuit.Base.CRel Gate n)
  where

open import Data.Nat.Base using (zero ; suc)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Circuit.Prop Gate Ex-gate
open Lift-To-Prop _SRel,_===_

private
  variable
    n : ℕ

-- The cycle that carries wire 0 to the top and every other wire one
-- down, and its inverse.
cyc cyc⁻ : (n : ℕ) → Circuit (₁₊ n)
cyc zero     = ε
cyc (suc n)  = σ • cyc n ↑
cyc⁻ zero    = ε
cyc⁻ (suc n) = cyc⁻ n ↑ • σ

cyc-cyc⁻ : ∀ n → (₁₊ n) ⊢ cyc n • cyc⁻ n ≈ ε
cyc-cyc⁻ zero    = PB.left-unit
cyc-cyc⁻ (suc n) =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (lemma-cong↑ (cyc n • cyc⁻ n) ε (cyc-cyc⁻ n)) PB.refl)
      PB.left-unit)))
    σ-invol)

cyc⁻-cyc : ∀ n → (₁₊ n) ⊢ cyc⁻ n • cyc n ≈ ε
cyc⁻-cyc zero    = PB.left-unit
cyc⁻-cyc (suc n) =
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong σ-invol PB.refl) PB.left-unit)))
    (lemma-cong↑ (cyc⁻ n • cyc n) ε (cyc⁻-cyc n)))

------------------------------------------------------------------------
-- The swap rules read backwards: a gate one wire up, then the cycle of
-- its own wires, is the cycle, then the gate.

private
  -- From g • N ≈ N • g′ and N N⁻ ≈ ε ≈ N⁻ N: g′ • N⁻ ≈ N⁻ • g.
  backwards : ∀ {g g′ N N⁻ : Circuit n} →
    n ⊢ g • N ≈ N • g′ → n ⊢ N • N⁻ ≈ ε → n ⊢ N⁻ • N ≈ ε → n ⊢ g′ • N⁻ ≈ N⁻ • g
  backwards e NN⁻ N⁻N =
    PB.trans (PB.sym PB.left-unit)
    (PB.trans (PB.cong (PB.sym N⁻N) PB.refl)
    (PB.trans PB.assoc
    (PB.cong PB.refl
      (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong (PB.sym e) PB.refl)
      (PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl NN⁻) PB.right-unit)))))))

  -- A cycle one wire longer: X ↑ then the swap, undone by the swap
  -- then X⁻ ↑.
  longer : ∀ {X X⁻ : Circuit (₁₊ n)} → (₁₊ n) ⊢ X • X⁻ ≈ ε →
    (₂₊ n) ⊢ (X ↑ • σ) • (σ • X⁻ ↑) ≈ ε
  longer {X = X} {X⁻} e =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong σ-invol PB.refl) PB.left-unit)))
      (lemma-cong↑ (X • X⁻) ε e))

  longer⁻ : ∀ {X X⁻ : Circuit (₁₊ n)} → (₁₊ n) ⊢ X⁻ • X ≈ ε →
    (₂₊ n) ⊢ (σ • X⁻ ↑) • (X ↑ • σ) ≈ ε
  longer⁻ {X = X} {X⁻} e =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong (lemma-cong↑ (X⁻ • X) ε e) PB.refl) PB.left-unit)))
      σ-invol)

  -- σ[ 2 ] = σ ↑ • σ and σ[ 3 ] = σ[ 2 ] ↑ • σ, with their inverses.
  N₂ N₂⁻ : Circuit (₃₊ n)
  N₂  = σ ↑ • σ
  N₂⁻ = σ • σ ↑

  N₃ N₃⁻ : Circuit (₄₊ n)
  N₃  = N₂ ↑ • σ
  N₃⁻ = σ • N₂⁻ ↑

  NN₂ : (₃₊ n) ⊢ N₂ • N₂⁻ ≈ ε
  NN₂ = longer σ-invol
  N₂⁻N₂ : (₃₊ n) ⊢ N₂⁻ • N₂ ≈ ε
  N₂⁻N₂ = longer⁻ σ-invol
  NN₃ : (₄₊ n) ⊢ N₃ • N₃⁻ ≈ ε
  NN₃ = longer NN₂
  N₃⁻N₃ : (₄₊ n) ⊢ N₃⁻ • N₃ ≈ ε
  N₃⁻N₃ = longer⁻ N₂⁻N₂

  -- The swap rules backwards: a gate one wire up passes the inverse
  -- cycle of its wires.
  swap₁ : (h : Gate 1) → (₂₊ n) ⊢ [ gate₁ h ]ʷ ↑ • σ ≈ σ • [ gate₁ h ]ʷ
  swap₁ h = backwards (sym-rule (σ-nat₁ h)) σ-invol σ-invol

  swap₂ : (h : Gate 2) → (₃₊ n) ⊢ [ gate₂ h ]ʷ ↑ • N₂⁻ ≈ N₂⁻ • [ gate₂ h ]ʷ
  swap₂ h = backwards (sym-rule (σ-nat₂ h)) NN₂ N₂⁻N₂

  swap₃ : (h : Gate 3) → (₄₊ n) ⊢ [ gate₃ h ]ʷ ↑ • N₃⁻ ≈ N₃⁻ • [ gate₃ h ]ʷ
  swap₃ h = backwards (sym-rule (σ-nat₃ h)) NN₃ N₃⁻N₃

------------------------------------------------------------------------
-- Naturality of the cycle

module _
  (scalars-comm : ∀ {n} (h h′ : Gate 0) →
     n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ)
  where

  open Central-Scalars scalars-comm using (comm-gate₀-w)

  -- One gate.
  nat-gen : (g : Gen n) → (₁₊ n) ⊢ [ g ]ʷ ↑ • cyc n ≈ cyc n • [ g ↧ ]ʷ
  nat-gen (gate₀ h) =
    PB.trans (PB.cong (PB.axiom (ω↑=ω h)) PB.refl)
      (PB.sym (comm-gate₀-w h (cyc _)))
  nat-gen {suc k} (gate₁ h) =
    PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (swap₁ h) PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.sym (comm-gate₁-w↑ h (cyc k))))
      (PB.sym PB.assoc))))
  nat-gen {suc (suc k)} (gate₂ h) =
    PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (swap₂ h) PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.sym (comm-gate₂-w↑↑ h (cyc k))))
    (PB.trans (PB.sym PB.assoc)
      (PB.cong PB.assoc PB.refl))))))
  nat-gen {suc (suc (suc k))} (gate₃ h) =
    PB.trans (PB.cong PB.refl (PB.trans (PB.cong PB.refl (PB.sym PB.assoc)) (PB.sym PB.assoc)))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (swap₃ h) PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.sym (comm-gate₃-w↑↑↑ h (cyc k))))
    (PB.trans (PB.sym PB.assoc)
      (PB.cong (PB.trans PB.assoc (PB.cong PB.refl PB.assoc)) PB.refl))))))
  nat-gen {suc k} (g ↥) =
    PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (PB.axiom (comm₂ Ex-gate g)) PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (lemma-cong↑ ([ g ]ʷ ↑ • cyc k) (cyc k • [ g ↧ ]ʷ) (nat-gen g)))
      (PB.sym PB.assoc))))

  -- A circuit: shifted one wire up, then the cycle, is the cycle, then
  -- the circuit with an idle wire on top.
  nat : (w : Circuit n) → (₁₊ n) ⊢ w ↑ • cyc n ≈ cyc n • w ⇓
  nat [ g ]ʷ  = nat-gen g
  nat ε       = PB.trans PB.left-unit (PB.sym PB.right-unit)
  nat (u • v) =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (nat v))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (nat u) PB.refl)
      PB.assoc)))

  -- So an idle wire on top is an idle wire at the bottom, moved by the
  -- cycle.
  top-is-bottom : (w : Circuit n) → (₁₊ n) ⊢ w ⇓ ≈ cyc⁻ n • w ↑ • cyc n
  top-is-bottom {n} w =
    PB.trans (PB.sym PB.left-unit)
    (PB.trans (PB.cong (PB.sym (cyc⁻-cyc n)) PB.refl)
    (PB.trans PB.assoc
      (PB.cong PB.refl (PB.sym (nat w)))))
