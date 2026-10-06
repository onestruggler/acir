------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed rotation against the gadget on four qubits (Clément,
-- Appendix E.5 at n = 4, rule (38), from Lemma D.5)
--
-- On four wires the gadget is the H gate HG = ΛH₀₁ (H on wire 0, box
-- wire 1, controls 2 3) white on the wires 2 3, and HGFrom reduces
-- HGRot 1 to its three canonical cases, the rotation's target on wire 0,
-- 1 or 3.  Each is proved in the frame of the transposition of the wires
-- 1 3, where HG is Lemma D.5's ΛH₂′ (box wire 3, controls 1 2) and the
-- rotations are fixed:
--
-- * C0, target on wire 0: X on wire 1 passes HG ((207)); white on wire
--   2 the H gate passes both rotations ((210), (211): they are words in
--   ΛH₂′ and the box on wire 1, which pass it by (181)), and white on
--   the wires 2 3 too, being the H gate white on wire 2 times °CH₂₀
--   ((171ᶜ) under the swap of the wires 1 2), which the rotations pass
--   ((232), (233)).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.HG
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; φ)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (°CH₂₀ ; module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L-sem ; O-L)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃ using (ΛH₂′ ; °ΛH₂′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃ using (eq171ᶜ ; ΛH₂′-°ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃ using (eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (eq210 ; eq211 ; eq214 ; eq214′ ; °ΛH₂′²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃ using (eq232 ; eq233)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (module T₁₃ ; T₁₃-via ; T₁₃-back ; T₁₃-N₂ ; T₁₃-N₃ ; T₁₃-ΛH₂′ ; S₂₃-ΛH₀₁ ; S₁₂-ΛH₂′ ; S₁₂-X₂ ; X₂-X₃)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; col-flip)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W4.Kit complete₂ complete₃ using (s12₄)

open Tools (4 VRel,_===_)
open WordAlgebra (4 VRel,_===_) using (comm-abab)

private
  HG G °G : Circuit 4
  HG = Ex ↓ • ΛH 2 • Ex ↓
  G  = ΛH₂′
  °G = °ΛH₂′

  R : Bool → Circuit 4
  R = rot {1}

  pass₂ : ∀ {a u v : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  passL : ∀ {a b y : Circuit 4} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
  passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

------------------------------------------------------------------------
-- The H gate passes the networks on the wires 2 3

private
  HG-gen : ∀ (g : S.Gen 2) → φ g ↑ ↑ • HG ≈ HG • φ g ↑ ↑
  HG-gen (S.gate₀ ())
  HG-gen (S.gate₁ ())
  HG-gen (S.gate₂ S.σ-gate)    = S₂₃.⟪⟫-comm S₂₃-ΛH₀₁
  HG-gen (S.gate₀ () S.↥)
  HG-gen (S.gate₁ () S.↥)
  HG-gen (S.gate₀ () S.↥ S.↥)

HG-rigid₄ : ∀ (v : Word (S.Gen 2)) → net v ↑ ↑ • HG ≈ HG • net v ↑ ↑
HG-rigid₄ [ g ]ʷ  = HG-gen g
HG-rigid₄ ε       = trans left-unit (sym right-unit)
HG-rigid₄ (u • v) = passL (HG-rigid₄ u) (HG-rigid₄ v)

------------------------------------------------------------------------
-- The frame of the transposition of the wires 1 3

private
  T₁₃R : ∀ β → T₁₃.⟪ R β ⟫ ≈ R β
  T₁₃R β = T₁₃-via (s23 β) (S₁₂.⟪⟫-fix (s12₄ β)) (s23 β)
    where
    s23 : ∀ β → S₂₃.⟪ R β ⟫ ≈ R β
    s23 true  = S₂₃.⟪⟫-fix (sym eq214)
    s23 false = S₂₃.⟪⟫-fix (sym eq214′)

  T₁₃HG : T₁₃.⟪ HG ⟫ ≈ G
  T₁₃HG = T₁₃-back T₁₃-ΛH₂′

  -- An equation with a rotation, carried back from the frame.
  unframe : ∀ β {W W′ : Circuit 4} → T₁₃.⟪ W ⟫ ≈ W′ → R β • W′ ≈ W′ • R β → R β • W ≈ W • R β
  unframe β {W} {W′} t e = T₁₃.⟪⟫-≈ e (T₁₃.⟪⟫-•₂ (T₁₃R β) (T₁₃-back t)) (T₁₃.⟪⟫-•₂ (T₁₃-back t) (T₁₃R β))

------------------------------------------------------------------------
-- C0: the target on the H gate's H wire

private
  -- White on wire 2, the H gate passes the rotations.
  °G-R : ∀ β → °G • R β ≈ R β • °G
  °G-R true  = trans (back _ eq210) (trans (comm-abab (sym ΛH₂′-°ΛH₂′) (sym eq181)) (front _ (sym eq210)))
  °G-R false = trans (back _ eq211) (trans (comm-abab (sym eq181) (sym ΛH₂′-°ΛH₂′)) (front _ (sym eq211)))

  -- White on the wires 1 2 (in the frame), it is the H gate white on
  -- wire 2 times °CH₂₀: the merge on wire 1.
  m₁ : G • N₁.⟪ G ⟫ ≈ CH₂₀
  m₁ = S₁₂.⟪⟫-≈ eq171ᶜ (S₁₂.⟪⟫-•₂ S₁₂-ΛH₂′ (S₁₂.⟪⟫-•₃ S₁₂-X₂ S₁₂-ΛH₂′ S₁₂-X₂)) (O-L CH)

  m₂ : °G • N₂.⟪ N₁.⟪ G ⟫ ⟫ ≈ °CH₂₀
  m₂ = trans (sym (N₂.⟪⟫-• G (N₁.⟪ G ⟫))) (N₂.⟪⟫-cong m₁)

  form₁₂ : N₂.⟪ N₁.⟪ G ⟫ ⟫ ≈ °G • °CH₂₀
  form₁₂ = trans (sym left-unit) (trans (front _ (sym °ΛH₂′²)) (trans assoc (back _ m₂)))

  R-°CH₂₀ : ∀ β → R β • °CH₂₀ ≈ °CH₂₀ • R β
  R-°CH₂₀ true  = sym eq232
  R-°CH₂₀ false = sym eq233

  W₁ : ∀ β → R β • N₂.⟪ N₁.⟪ G ⟫ ⟫ ≈ N₂.⟪ N₁.⟪ G ⟫ ⟫ • R β
  W₁ β = trans (back _ form₁₂) (trans (pass₂ (sym (°G-R β)) (R-°CH₂₀ β)) (front _ (sym form₁₂)))

  -- The gadget's colourings, as conjugations.
  cTT : col (true ∷ true ∷ false ∷ true ∷ []) HG ≈ N₂.⟪ HG ⟫
  cTT = cong right-unit (back _ right-unit)

  cTF : col (true ∷ true ∷ false ∷ false ∷ []) HG ≈ N₂.⟪ N₃.⟪ HG ⟫ ⟫
  cTF = begin
    (X ↑ ↑ • (X ↑ ↑ ↑ • ε)) • HG • (X ↑ ↑ • (X ↑ ↑ ↑ • ε))
      ≈⟨ cong (back _ right-unit) (back _ (back _ right-unit)) ⟩
    (X ↑ ↑ • X ↑ ↑ ↑) • HG • (X ↑ ↑ • X ↑ ↑ ↑)
      ≈⟨ back _ (back _ X₂-X₃) ⟩
    (X ↑ ↑ • X ↑ ↑ ↑) • HG • (X ↑ ↑ ↑ • X ↑ ↑)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    N₂.⟪ N₃.⟪ HG ⟫ ⟫ ∎

  -- X on the box wire passes HG.
  xh : X ↑ • HG ≈ HG • X ↑
  xh = S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ sX refl) (S₀₁.⟪⟫-•₂ refl sX)
    where
    sX : S₀₁.⟪ X ⟫ ≈ X ↑
    sX = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  C0t : ∀ β c → R β • col (true ∷ true ∷ false ∷ c ∷ []) HG ≈ col (true ∷ true ∷ false ∷ c ∷ []) HG • R β
  C0t β true  = trans (back _ cTT) (trans (unframe β (T₁₃-N₂ T₁₃HG) (sym (°G-R β))) (front _ (sym cTT)))
  C0t β false = trans (back _ cTF) (trans (unframe β (T₁₃-N₂ (T₁₃-N₃ T₁₃HG)) (W₁ β)) (front _ (sym cTF)))

C0₄ : ∀ β (z : Bits 4) → lookupℕ 0 z ≡ true → lookupℕ 2 z ≡ false → R β • col z HG ≈ col z HG • R β
C0₄ β (true ∷ true  ∷ false ∷ c ∷ []) _ _ = C0t β c
C0₄ β (true ∷ false ∷ false ∷ c ∷ []) _ _ = trans (back _ e) (trans (C0t β c) (front _ (sym e)))
  where
  e : col (true ∷ false ∷ false ∷ c ∷ []) HG ≈ col (true ∷ true ∷ false ∷ c ∷ []) HG
  e = col-flip (sF 0F) (true ∷ true ∷ false ∷ c ∷ []) xh
C0₄ β (false ∷ _)              () _
C0₄ β (true ∷ b ∷ true ∷ _)    _  ()
