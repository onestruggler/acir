------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical form of rule (45) of Figure 8 (Clément, Lemma 8.8)
--
-- At width 5 + k, with Λ the box on wire 0, A = ΛH the H gate on wire 0
-- with its box wire on wire 1 (P ⊗ P around Λ, by definition), Zc = Λ
-- negated on wire 1 and Cw the H gate on wire 0 with its box wire on
-- wire 2, white on wire 1, as the decoding spells it:
--
--   A • Zc • Cw • A • Cw ≈ Cw • A • Cw • Zc • A                 (`core45`)
--
-- which is what rule (45) decodes to once the negations common to its
-- letters are conjugated away (Lemma88.Rule45).  All five letters are
-- involutions, so it says that the word is one.  The paper's proof is
-- six pages ((311), (337), (344), (309), (310), (277), (274), (308));
-- here it is the three-qubit proof of (146) with multiple controls:
--
--   * Cw is X on wire 1 around G, the H gate HG = Col.Hg under the swap
--     of the wires 1 2 ((338)'s X-Hg, and XY.S-ΛH);
--   * Zc = Λ M with M the box on wire 1, wire 0 idle ((309)), and M
--     passes A, Λ, X on wire 1 and G ((276), (335), (338)), so it
--     cancels from both sides: what is left is T′ = A Λ Cw′ A Cw′ equal
--     to its reverse;
--   * between P ⊗ P on the wires 0 1, A and Λ exchange, and Cw′ becomes
--     Ct Mx, with Ct = G under the swap of the wires 0 1 and Mx = K XK
--     the box on wire 2 with wire 1 idle (the Klein four-group of P ⊗ P
--     on the three lower wires, `Base45`); Mx passes Λ and Ct and is an
--     involution, so it cancels too;
--   * (Ct Λ)² ≈ (A K)², both being ΛZX by (333) under the swaps, the
--     first through (353) — and then Λ A Ct Λ Ct and its reverse are
--     both Λ K A K Λ.
--
-- The argument is Canon45Gen's, generic in the width; this is its
-- instance from five wires on, the box facts from canonN, (335) and (336)
-- (BoxComm), (276) (ZXPass), the H gate Col.Hg with (338) (Box338,
-- Box338Eq) and (333) (Canon40, ZX353).  Every step was checked
-- numerically at four to seven wires first (scratchpad r4x/plan45.py,
-- review-r45.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon45
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Nat using (ℕ ; suc ; s≤s)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (box276)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (S-ZX ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃ using (eq333)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (sep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ)
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon45Gen complete₂ complete₃ as G45

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)
  open XY k below using (eq338xy ; X-Hg ; S-ΛH)

  private
    Λ B HG : Circuit N
    Λ  = Λ□ (₄₊ k)
    B  = Ex ↓ • Λ • Ex ↓
    HG = Hg (₂₊ k)

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    S₁₂-Λ : Ex ↑ • Λ • Ex ↑ ≈ Λ
    S₁₂-Λ = trans (sym assoc) (trans (front _ (symAt 0)) (trans assoc (trans (back _ Ex↑²) right-unit)))

    -- The colourings white on wire 1, resp. on wire 2.
    colZc : col (true ∷ false ∷ replicate (₃₊ k) true) Λ ≈ X ↑ • Λ • X ↑
    colZc = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) ↑ • Λ • (X • z ↑) ↑) (allT (₃₊ k))))
                  (cong right-unit (back _ right-unit))

    colX₂ : ∀ w → col (true ∷ true ∷ false ∷ replicate (₂₊ k) true) w ≈ X ↑ ↑ • w • X ↑ ↑
    colX₂ w = trans (≡→≈ (Eq.cong (λ z → ((X • z ↑) ↑) ↑ • w • ((X • z ↑) ↑) ↑) (allT (₂₊ k))))
                    (cong right-unit (back _ right-unit))

    Λ-Zc : Λ • (X ↑ • Λ • X ↑) ≈ (X ↑ • Λ • X ↑) • Λ
    Λ-Zc = trans (back _ (sym colZc)) (trans (eq335 k below (true ∷ false ∷ replicate (₃₊ k) true)) (front _ colZc))

    PP-M : PP ↓ • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • PP ↓
    PP-M = sym (conj-comm eq111 (box276 (suc k) c))

    sepΛ : Λ • (X ↑ ↑ • HG • X ↑ ↑) ≈ (X ↑ ↑ • HG • X ↑ ↑) • Λ
    sepΛ = trans (back _ (sym (colX₂ HG))) (trans (sep k below (replicate (₂₊ k) true)) (front _ (colX₂ HG)))

    c336′ : Λ • (X ↑ ↑ • B • X ↑ ↑) ≈ (X ↑ ↑ • B • X ↑ ↑) • Λ
    c336′ = trans (back _ (sym (colX₂ B)))
                  (trans (eq336ᶜ k below (true ∷ true ∷ false ∷ replicate (₂₊ k) true)) (front _ (colX₂ B)))

    c335′ : Λ • (X ↑ ↑ • Λ • X ↑ ↑) ≈ (X ↑ ↑ • Λ • X ↑ ↑) • Λ
    c335′ = trans (back _ (sym (colX₂ Λ)))
                  (trans (eq335 k below (true ∷ true ∷ false ∷ replicate (₂₊ k) true)) (front _ (colX₂ Λ)))

  ------------------------------------------------------------------------
  -- Rule (45), canonical

  open G45 {₁₊ k} canon HG refl S-ΛH X-Hg eq338xy S₁₂-Λ Λ-Zc PP-M sepΛ c336′ c335′ (eq333 k below) (S-ZX k below)
    public using (core45)
