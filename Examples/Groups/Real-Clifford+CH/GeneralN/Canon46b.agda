------------------------------------------------------------------------
-- Presentations of groups
--
-- Rule (46) of Figure 8 at the canonical position (Clément, Lemma 8.8)
--
-- Canon46a reduces Core46 to the commutation of UA F UA and UB K UB,
-- with K = K₁ K₂; that is F against V K V⁻¹ with V = UA UB.  Between
-- P ⊗ P on the wires 0 1 (`PF`, `PM`):
--
--   F ↦ Vh Fo, the H gate on wire 1 with its box wire 2, black on
--   wire 0, and the box on wire 2 with wire 1 idle, black on wire 0;
--   K₁ ↦ C0, K₂ ↦ G′, the box on wire 1 and the H gate on wire 1 with
--   its box wire 2, both white on wire 0;
--   UA UB ↦ ζ η, a circuit on the wires 1 2, which splits over the
--   colour of wire 0 into Vo (white) and Vc (black), words in the box on
--   wire 3 of the bottom four wires (Base46).
--
-- So what is to show is that Vh Fo passes Vo (C0 G′) Vo⁻¹, where Vc,
-- black on wire 0, has passed C0 G′: every gate there is separated from
-- the other side by the colour of wire 0.  The pairs are (339) — the
-- four-wire box against the H gate, under the relabellings πa, πb of
-- the bottom four wires (`C339₄`: the four-wire box is the product of
-- the box over every colouring of the wires 4 …, merge-top₃) — (338)
-- with x ≠ y, and boxes against boxes ((335), (336)).  The argument is
-- Canon46bGen's, generic in the width; this is its instance from five
-- wires on, the four-wire steps (Base46) evaluated with completeness on
-- four qubits and (339) for the four-wire box from Box339 over every
-- colouring of the wires 4 … (merge-top₃).  Each was checked numerically
-- first (scratchpad t46b.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon46b
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true)
open import Data.Nat using (ℕ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (_∷_ ; replicate)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (pass-∏)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box339 complete₂ complete₃ using (eq339)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box337 complete₂ complete₃ using (col-2)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box337 complete₂ complete₃ using (eq337)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon46a complete₂ complete₃ using (module At)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base46At using (Base46At)
import Examples.Groups.Real-Clifford+CH.GeneralN.Base46 as B46
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon46bGen complete₂ complete₃ as G46b

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m′ : ℕ
    N  = ₁₊ (₄₊ k)
    m′ = ₁₊ k

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    Λ₀ : Circuit N
    Λ₀ = Λ□ (₄₊ k)

  open Tools (N VRel,_===_)
  open At k below using (canon ; HG ; S-ΛH ; X-Hg ; eq338xy ; s12Λ₀ ; mt ; sepΛ ; eq339c′ ; PYo′)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₃)

  private
    via : ∀ {y u w : Circuit N} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    via′ : ∀ {y u w : Circuit N} → u ≈ w → w • y ≈ y • w → u • y ≈ y • u
    via′ e p = trans (front _ e) (trans p (back _ (sym e)))

    ev : ∀ {u v : Circuit 4} → Evaluated u v → (u ↓ᵏ m′) ≈ (v ↓ᵏ m′)
    ev {u} {v} e = by-sem u v (Evaluated.same e) {m′}

    -- The four-wire steps, evaluated.
    b46 : Base46At m′
    b46 = record
      { ea₁ = ev B46.ea₁ ; ea₂ = ev B46.ea₂ ; eb₁ = ev B46.eb₁ ; eb₂ = ev B46.eb₂
      ; ea-bb = ev B46.ea-bb ; eb-bb = ev B46.eb-bb
      ; ea-X = ev B46.ea-X ; ea-X₁ = ev B46.ea-X₁ ; ea-P = ev B46.ea-P ; ea-L = ev B46.ea-L ; ea-R = ev B46.ea-R
      ; eb-X = ev B46.eb-X ; eb-X₂ = ev B46.eb-X₂ ; eb-P = ev B46.eb-P ; eb-L = ev B46.eb-L ; eb-R = ev B46.eb-R
      ; e-X₂P = ev B46.e-X₂P ; e-ζη = ev B46.e-ζη ; e-Vc = ev B46.e-Vc }

    -- (339): the four-wire box, as the box over every colouring of the
    -- wires 4 …, against the H gate on wire 3 with its box wire 1, white
    -- on wire 2.
    C339₄ : (Λ□ 3 ↓ᵏ m′) • (X ↑ ↑ • Hg₃ m′ • X ↑ ↑) ≈ (X ↑ ↑ • Hg₃ m′ • X ↑ ↑) • (Λ□ 3 ↓ᵏ m′)
    C339₄ = via (sym (col-2 (Hg₃ m′)))
              (via′ (sym (merge-top₃ m′ ≤-refl))
                    (sym (pass-∏ (allBits m′) (λ x → col (true ∷ true ∷ true ∷ true ∷ x) Λ₀)
                                 (λ x → sym (eq339 k below true x (replicate m′ true))))))

  open G46b {₁₊ k} canon HG refl S-ΛH X-Hg eq338xy s12Λ₀ mt (eq335 k below) (eq336ᶜ k below) sepΛ
            (eq337 k below) eq339c′ PYo′ (symAt 1) (merge-top₃ m′ ≤-refl) C339₄ b46 public using (core46)
