------------------------------------------------------------------------
-- Presentations of groups
--
-- The structural commutations of the bottom wires against the top
--
-- Derived from the structural rules alone, so that a module using them
-- does not load the swap rules and, through them, completeness on three
-- wires (Four.Chain, Four.D: loading their imports takes 6 s instead of
-- 20).  TopWeakening.low-comm and Idle.low₁-comm are the same lemmas
-- with the same proofs, kept there since moving them changes those
-- modules' interfaces and so rechecks everything above them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.LowComm where

open import Data.Nat using (ℕ)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

private
  variable
    n : ℕ

-- A circuit on the bottom wire passes one on the wires above it.
low₁-comm : (u : Circuit 1) (v : Circuit n) → (₁₊ n) ⊢ (u ↓ᵏ n) • v ↑ ≈ v ↑ • (u ↓ᵏ n)
low₁-comm {n} [ gate₀ h ]ʷ v = PB.sym (comm-gate₀-w h (v ↑))
low₁-comm {n} [ gate₀ h ↥ ]ʷ v = lemma-cong↑ ([ gate₀ h ]ʷ • v) (v • [ gate₀ h ]ʷ) (PB.sym (comm-gate₀-w h v))
low₁-comm {n} [ gate₁ h ]ʷ v = PB.sym (comm-gate₁-w↑ h v)
low₁-comm {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₁₊ n) VRel,_===_)
low₁-comm {n} (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • v ↑   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • v ↑)   ≈⟨ back _ (low₁-comm t v) ⟩
  (u ↓ᵏ n) • (v ↑ • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • v ↑) • (t ↓ᵏ n)   ≈⟨ front _ (low₁-comm u v) ⟩
  (v ↑ • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  v ↑ • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools ((₁₊ n) VRel,_===_)

-- A circuit on the bottom two wires passes one on the wires above them.
low-comm : (u : Circuit 2) (v : Circuit n) → (₂₊ n) ⊢ (u ↓ᵏ n) • v ↑ ↑ ≈ v ↑ ↑ • (u ↓ᵏ n)
low-comm {n} [ gate₀ h ]ʷ v = PB.sym (comm-gate₀-w h (v ↑ ↑))
low-comm {n} [ gate₀ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₀ h ]ʷ • v ↑) (v ↑ • [ gate₀ h ]ʷ) (PB.sym (comm-gate₀-w h (v ↑)))
low-comm {n} [ gate₀ h ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₀ h ↥ ]ʷ • v ↑) (v ↑ • [ gate₀ h ↥ ]ʷ)
    (lemma-cong↑ ([ gate₀ h ]ʷ • v) (v • [ gate₀ h ]ʷ) (PB.sym (comm-gate₀-w h v)))
low-comm {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑))
  where open Tools ((₂₊ n) VRel,_===_)
low-comm {n} [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h v)
  where open Tools ((₂₊ n) VRel,_===_)
low-comm {n} [ gate₁ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h v))
  where open Tools ((₁₊ n) VRel,_===_) renaming (sym to PB-sym)
low-comm {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₂₊ n) VRel,_===_)
low-comm {n} (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • v ↑ ↑   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • v ↑ ↑)   ≈⟨ back _ (low-comm t v) ⟩
  (u ↓ᵏ n) • (v ↑ ↑ • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • v ↑ ↑) • (t ↓ᵏ n)   ≈⟨ front _ (low-comm u v) ⟩
  (v ↑ ↑ • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  v ↑ ↑ • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools ((₂₊ n) VRel,_===_)
