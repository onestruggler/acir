------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled circuits under idle wires: ctrl commutes with padding, and
-- a circuit one wire up is controlled through CTRL₁.
--
-- Every gadget is a closed word, so an idle wire on top widens it to
-- the same gadget one wire wider (`CTRL-pad`), except where the circuit
-- is too narrow for its borrowed wire (HH on two wires, CCX on three);
-- from four wires on that never happens (`ctrl-pad`).  A circuit
-- shifted one wire up is controlled gate by gate through CTRL₁
-- (`ctrl-↑`), and one more wire up conjugates that by the swaps of
-- wires 1 2 and 0 1 (`ctrl₁-↑`, up to the cancellation of the swaps
-- between consecutive gates).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.CtrlPad where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Syntactics
open import Examples.Groups.CCX+HH.NaturalP.Ctrl
open import Examples.Groups.CCX+HH.NaturalP.Pad using (↑↓)

private
  variable
    n m j : ℕ

------------------------------------------------------------------------
-- Padding

-- CTRL₁ is never degenerate.
CTRL₁-pad : (g : Gen m) (j : ℕ) → CTRL₁ (g ↧ᵏ j) ≡ CTRL₁ g ↓ᵏ j
CTRL₁-pad (gate₀ ()) j
CTRL₁-pad (gate₁ X-gate) j   = Eq.refl
CTRL₁-pad (gate₂ CX-gate) j  = Eq.refl
CTRL₁-pad (gate₂ SW-gate) j  = Eq.refl
CTRL₁-pad (gate₂ HH-gate) j  = Eq.refl
CTRL₁-pad (gate₃ CCX-gate) j = Eq.refl
CTRL₁-pad (g ↥) j =
  Eq.cong (λ x → (σ ↑ • σ) • x • (σ • σ ↑))
    (Eq.trans (Eq.cong _↑ (CTRL₁-pad g j)) (Eq.sym (↑↓ (CTRL₁ g) j)))

-- CTRL on four or more wires.
CTRL-pad : (g : Gen (₄₊ n)) (j : ℕ) → CTRL (g ↧ᵏ j) ≡ CTRL g ↓ᵏ j
CTRL-pad (gate₀ ()) j
CTRL-pad (gate₁ X-gate) j   = Eq.refl
CTRL-pad (gate₂ CX-gate) j  = Eq.refl
CTRL-pad (gate₂ SW-gate) j  = Eq.refl
CTRL-pad (gate₂ HH-gate) j  = Eq.refl
CTRL-pad (gate₃ CCX-gate) j = Eq.refl
CTRL-pad (g ↥) j            = CTRL₁-pad g j

ctrl-pad : (w : Circuit (₄₊ n)) (j : ℕ) → ctrl (w ↓ᵏ j) ≡ ctrl w ↓ᵏ j
ctrl-pad [ g ]ʷ  j = CTRL-pad g j
ctrl-pad ε       j = Eq.refl
ctrl-pad (u • v) j = Eq.cong₂ _•_ (ctrl-pad u j) (ctrl-pad v j)

------------------------------------------------------------------------
-- One wire up

-- A circuit on the wires 2 … m + 1, controlled by wire 0, wire 1 spare.
ctrl₁ : Circuit m → Circuit (₂₊ m)
ctrl₁ [ g ]ʷ  = CTRL₁ g
ctrl₁ ε       = ε
ctrl₁ (u • v) = ctrl₁ u • ctrl₁ v

ctrl-↑ : (w : Circuit m) → ctrl (w ↑) ≡ ctrl₁ w
ctrl-↑ [ g ]ʷ  = Eq.refl
ctrl-↑ ε       = Eq.refl
ctrl-↑ (u • v) = Eq.cong₂ _•_ (ctrl-↑ u) (ctrl-↑ v)

ctrl₁-pad : (w : Circuit m) (j : ℕ) → ctrl₁ (w ↓ᵏ j) ≡ ctrl₁ w ↓ᵏ j
ctrl₁-pad [ g ]ʷ  j = CTRL₁-pad g j
ctrl₁-pad ε       j = Eq.refl
ctrl₁-pad (u • v) j = Eq.cong₂ _•_ (ctrl₁-pad u j) (ctrl₁-pad v j)

-- One more wire up: the swaps of wires 1 2 and 0 1 around the circuit,
-- once the swaps between consecutive gates cancel.
ctrl₁-↑ : (w : Circuit m) → (₃₊ m) ⊢ ctrl₁ (w ↑) ≈ (σ ↑ • σ) • ctrl₁ w ↑ • (σ • σ ↑)
ctrl₁-↑ [ g ]ʷ  = PB.refl
ctrl₁-↑ ε       = PB.sym (PB.trans (PB.cong PB.refl PB.left-unit) cancel)
  where
  cancel : (₃₊ _) ⊢ (σ ↑ • σ) • (σ • σ ↑) ≈ ε
  cancel = PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong σ-invol PB.refl) PB.left-unit)))
      (lemma-cong↑ (σ • σ) ε σ-invol))
ctrl₁-↑ (u • v) =
  PB.trans (PB.cong (ctrl₁-↑ u) (ctrl₁-↑ v)) merge
  where
  L = σ ↑ • σ
  L⁻ = σ • σ ↑
  U = ctrl₁ u ↑
  V = ctrl₁ v ↑
  LL⁻ : (₃₊ _) ⊢ L⁻ • L ≈ ε
  LL⁻ = PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong (lemma-cong↑ (σ • σ) ε σ-invol) PB.refl) PB.left-unit)))
      σ-invol)
  merge : (₃₊ _) ⊢ (L • U • L⁻) • (L • V • L⁻) ≈ L • (U • V) • L⁻
  merge =
    PB.trans PB.assoc
    (PB.cong PB.refl
      (PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl
        (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong LL⁻ PB.refl) PB.left-unit)))
      (PB.sym PB.assoc))))
