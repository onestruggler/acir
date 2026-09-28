------------------------------------------------------------------------
-- Presentations of groups
--
-- The wires of the Maslov decomposition: its Toffoli-4 gate touches
-- its four wires, and the paper's layout covers every wire (Amy,
-- QPL 2018, table 2)
--
-- Table 2's first column counts qubits as the paper's tool does: the
-- wires some gate of the circuit touches (PathSum.CRK.Qubits.qubits;
-- a Hadamard or a phase gate touches its wire, a CNOT its control and
-- its target).  PathSum.Maslov proves that the Maslov decomposition
-- touches every control, the target and every ancilla of its layout,
-- so that on the paper's layout its qubits are all n + ⌈(n − 3)/2⌉
-- of its wires (Maslovₙ-qubits).  This module holds the two facts
-- that proof rests on which do not mention the construction:
--
-- * the relative-phase Toffoli-4 gate rc3x a b c d touches its four
--   wires: d with its first gate (H d), c with its third (CNOT c d),
--   a with its sixth (CNOT a d), b with its eighth (CNOT b d)
--   (∈ᶜ-rc3x; the tool's sixteen-gate Toffoli circuit touches its
--   three, PathSum.Adder.Tool.∈ᶜ-tof₃);
--
-- * every wire of the paper's layout is a control, the target or an
--   ancilla: on n + ⌈(n − 3)/2⌉ wires the controls are wires
--   0 … n − 2, the target wire n − 1 and the ancillas the wires from
--   n on, which leaves no wire out (layout-wires, standardᴹ-wires; by
--   Fin's splitAt at the first n wires, and every wire of those being
--   the last or below it, last-or-inject₁).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov.Wires (M₀ : ℕ) where

open import Data.Fin.Base using
  (Fin; zero; suc; fromℕ; inject₁; splitAt)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using
  (zero; _+_; _∸_; _≤_; z≤n; s≤s; ⌊_/2⌋; ⌈_/2⌉)
open import Data.Product.Base using (∃; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; cong)

import Data.Fin.Properties as Fin

open import PathSum.CRK.Qubits M₀ using (_∈ᶜ_)
open import PathSum.Maslov.Chain M₀ using
  (ctl; tgt; anc; layout; standardᴹ)
open import PathSum.Maslov.Gate4 M₀ using (rc3x)

private
  variable
    n k : ℕ


------------------------------------------------------------------------
-- The relative-phase Toffoli-4 gate touches its four wires

-- d with its first gate (H d), c with its third (CNOT c d), a with its
-- sixth (CNOT a d), b with its eighth (CNOT b d).

∈ᶜ-rc3x : (a b c d : Fin n) (p : a ≢ d) (q : b ≢ d) (r : c ≢ d)
          {u : Fin n} → u ∈ a ∷ b ∷ c ∷ d ∷ [] → u ∈ᶜ rc3x a b c d p q r
∈ᶜ-rc3x a b c d p q r (here refl)                         =
  there (there (there (there (there (here (here refl))))))
∈ᶜ-rc3x a b c d p q r (there (here refl))                 =
  there (there (there (there (there (there (there (here (here refl))))))))
∈ᶜ-rc3x a b c d p q r (there (there (here refl)))         =
  there (there (here (here refl)))
∈ᶜ-rc3x a b c d p q r (there (there (there (here refl)))) = here (here refl)


------------------------------------------------------------------------
-- The paper's layout covers every wire

-- A wire of Fin (k + 1) is the last one, k, or one below it.

last-or-inject₁ : (v : Fin (suc k)) → v ≡ fromℕ k ⊎ ∃ λ i → v ≡ inject₁ i
last-or-inject₁ {zero}  zero     = inj₁ refl
last-or-inject₁ {zero}  (suc ())
last-or-inject₁ {suc k} zero     = inj₂ (zero , refl)
last-or-inject₁ {suc k} (suc v)  with last-or-inject₁ v
... | inj₁ e       = inj₁ (cong suc e)
... | inj₂ (i , e) = inj₂ (suc i , cong suc e)

-- For m + 1 controls, on m + 2 + ⌊m/2⌋ wires: every wire is a control
-- (wires 0 … m), the target (wire m + 1) or an ancilla (the wires from
-- m + 2 on).

layout-wires : (m : ℕ) (u : Fin (suc (suc m) + ⌊ m /2⌋)) →
               (∃ λ i → u ≡ ctl (layout m) i) ⊎ u ≡ tgt (layout m) ⊎
               (∃ λ j → u ≡ anc (layout m) j)
layout-wires m u = go (splitAt (suc (suc m)) u) refl
  where
  go : (s : Fin (suc (suc m)) ⊎ Fin ⌊ m /2⌋) → splitAt (suc (suc m)) u ≡ s →
       (∃ λ i → u ≡ ctl (layout m) i) ⊎ u ≡ tgt (layout m) ⊎
       (∃ λ j → u ≡ anc (layout m) j)
  go (inj₁ v) e with last-or-inject₁ v
  ... | inj₁ refl       = inj₂ (inj₁ (sym (Fin.splitAt⁻¹-↑ˡ e)))
  ... | inj₂ (i , refl) = inj₁ (i , sym (Fin.splitAt⁻¹-↑ˡ e))
  go (inj₂ j) e = inj₂ (inj₂ (j , sym (Fin.splitAt⁻¹-↑ʳ e)))

-- For every n ≥ 3, on n + ⌈(n − 3)/2⌉ wires: every wire is a control
-- (wires 0 … n − 2), the target (wire n − 1) or an ancilla (the wires
-- from n on).

standardᴹ-wires : (n : ℕ) (p : 3 ≤ n) (u : Fin (n + ⌈ n ∸ 3 /2⌉)) →
                  (∃ λ i → u ≡ ctl (standardᴹ n p) i) ⊎
                  u ≡ tgt (standardᴹ n p) ⊎
                  (∃ λ j → u ≡ anc (standardᴹ n p) j)
standardᴹ-wires (suc (suc (suc m))) (s≤s (s≤s (s≤s z≤n))) =
  layout-wires (suc m)
