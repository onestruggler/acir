------------------------------------------------------------------------
-- Presentations of groups
--
-- The core of rule (46) on four qubits (Clément, Appendix E.5 at n = 4,
-- from Lemma D.5)
--
-- Canon46aGen's and Canon46bGen's argument at width four.  The box facts
-- come from canon4 and W4.Box ((335), (336) in every colouring), the
-- merge of the box over the colour of wire 3 is (170₃), (337) is (196ᵈ)
-- under the swap of the wires 2 3 and (276) is disjointness; the H gate
-- is ΛH₀₁ itself, with (338) for x = y (W4.Cores), (194) under X on wire
-- 2, X on its box wire ((207)) and (339) against the box on wire 2 white
-- on wire 3, which is (185) under the swaps.  The four-wire steps and
-- (339) for the box are Lemma88.W4.Base46W4.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Core46
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq157 ; eq161 ; eq162)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃ using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃ using (eq185)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq170₃ ; eq194 ; eq196ᵈ ; S₂₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃ using (ΛH₀₁-PP)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃ using (eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (S₁₂-X₃ ; S₂₃-X₂ ; S₂₃-X₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
import Examples.Groups.Real-Clifford+CH.GeneralN.Canon46bGen complete₂ complete₃ as G46b
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letters46 using (Core46)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Box complete₂ complete₃ using (c335₁ ; c336₁)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Cores complete₂ complete₃ using (HG-box₃)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Base46W4 complete₂ complete₃ using (base46₄ ; c339₄)

open Tools (4 VRel,_===_)

private
  HG : Circuit 4
  HG = Ex ↓ • ΛH 2 • Ex ↓

  sX : S₀₁.⟪ X ⟫ ≈ X ↑
  sX = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  -- X on the box wire passes HG ((207)).
  X-Hg : X ↑ • HG ≈ HG • X ↑
  X-Hg = S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ sX refl) (S₀₁.⟪⟫-•₂ refl sX)

  -- (338) with the colourings differing on wire 2: (194) under X there.
  sepΛ : box₃ • (X ↑ ↑ • HG • X ↑ ↑) ≈ (X ↑ ↑ • HG • X ↑ ↑) • box₃
  sepΛ = N₂.⟪⟫-≈ (sym eq194) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ box₃) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ box₃))

  -- The box over the colours of wire 3 is the CZ of the wires 1 2 ((170₃)).
  mt : (((X ↑ ↑ ↑ • ε) • box₃ • (X ↑ ↑ ↑ • ε)) • ((ε • box₃ • ε) • ε)) ≈ CZ ↑
  mt = begin
    ((X ↑ ↑ ↑ • ε) • box₃ • (X ↑ ↑ ↑ • ε)) • ((ε • box₃ • ε) • ε)
      ≈⟨ back _ (trans right-unit (trans left-unit right-unit)) ⟩
    ((X ↑ ↑ ↑ • ε) • box₃ • (X ↑ ↑ ↑ • ε)) • box₃
      ≈⟨ sym (c335₁ (true ∷ true ∷ true ∷ false ∷ [])) ⟩
    box₃ • ((X ↑ ↑ ↑ • ε) • box₃ • (X ↑ ↑ ↑ • ε))
      ≈⟨ back _ (cong right-unit (back _ right-unit)) ⟩
    box₃ • N₃.⟪ box₃ ⟫
      ≈⟨ eq170₃ ⟩
    CZ ↑ ∎

  -- (337): the box against ΛH white on wire 2, (196ᵈ) under the swap of
  -- the wires 2 3.
  eq337₄ : box₃ • (X ↑ ↑ • ΛH 2 • X ↑ ↑) ≈ (X ↑ ↑ • ΛH 2 • X ↑ ↑) • box₃
  eq337₄ = S₂₃.⟪⟫-≈ eq196ᵈ (S₂₃.⟪⟫-•₂ eq161 sN) (S₂₃.⟪⟫-•₂ sN eq161)
    where
    sN : S₂₃.⟪ N₃.⟪ ΛH 2 ⟫ ⟫ ≈ X ↑ ↑ • ΛH 2 • X ↑ ↑
    sN = S₂₃.⟪⟫-•₃ S₂₃-X₃ eq162 S₂₃-X₃

  -- (339): the box on wire 2 against HG white on wire 3, (185) under the
  -- swaps.
  e185 : (Ex ↑ • box₃′ • Ex ↑) • N₃.⟪ HG ⟫ ≈ N₃.⟪ HG ⟫ • (Ex ↑ • box₃′ • Ex ↑)
  e185 = trans (sym (cong sB sH)) (trans eq185 (cong sH sB))
    where
    sB : S₁₂.⟪ S₂₃.⟪ box₃′ ⟫ ⟫ ≈ Ex ↑ • box₃′ • Ex ↑
    sB = S₁₂.⟪⟫-cong S₂₃-box₃′
    sH : S₁₂.⟪ S₂₃.⟪ °ΛH₂′ ⟫ ⟫ ≈ N₃.⟪ HG ⟫
    sH = trans (S₁₂.⟪⟫-cong (S₂₃.⟪⟫-•₃ S₂₃-X₂ (S₂₃.⟪⟫-⟪⟫ (S₁₂.⟪ HG ⟫)) S₂₃-X₂))
               (S₁₂.⟪⟫-•₃ S₁₂-X₃ (S₁₂.⟪⟫-⟪⟫ HG) S₁₂-X₃)

  eq339c₄ : ∀ (c : Bits 1) → c ≢ replicate 1 true →
            (Ex ↑ • box₃′ • Ex ↑) • (negsB (true ∷ true ∷ true ∷ c) • HG • negsB (true ∷ true ∷ true ∷ c))
            ≈ (negsB (true ∷ true ∷ true ∷ c) • HG • negsB (true ∷ true ∷ true ∷ c)) • (Ex ↑ • box₃′ • Ex ↑)
  eq339c₄ (true ∷ [])  ne = ⊥-elim (ne Eq.refl)
  eq339c₄ (false ∷ []) _  = trans (back _ cc) (trans e185 (front _ (sym cc)))
    where
    cc : (X ↑ ↑ ↑ • ε) • HG • (X ↑ ↑ ↑ • ε) ≈ N₃.⟪ HG ⟫
    cc = cong right-unit (back _ right-unit)

  -- P ⊗ P on the wires 0 1 passes the CZ of the wires 2 3.
  PYo′ : PP ↓ • CZ ↑ ↑ • PP ↓ ≈ CZ ↑ ↑
  PYo′ = trans (sym assoc) (trans (front _ (low-comm PP CZ))
           (trans assoc (trans (back _ (L-sem (PP • PP) ε Eq.refl)) right-unit)))

  -- The swap of the wires 2 3 passes the box ((161)).
  sym1 : Ex ↑ ↑ • box₃ ≈ box₃ • Ex ↑ ↑
  sym1 = sym (conj-comm (lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)) eq161)

  -- With no wires above 3 the four-wire box is the box.
  mt3 : ((ε • box₃ • ε) • ε) ≈ box₃
  mt3 = trans right-unit (trans left-unit right-unit)

core46₁ : Core46 {1}
core46₁ = G46b.core46 {0} canon4 HG ΛH₀₁-PP refl X-Hg (sym HG-box₃) eq157 mt c335₁ c336₁ sepΛ eq337₄ eq339c₄
            PYo′ sym1 mt3 c339₄ base46₄
