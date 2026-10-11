------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical cores of rules (39) and (40) on four qubits (Clément,
-- Appendix E.5 at n = 4, from Lemma D.5)
--
-- On four wires the H gate of the decoding is HG = Ex ↓ • ΛH 2 • Ex ↓,
-- Lemma D.5's ΛH₀₁: H on wire 0, box wire 1, controls 2 3.
--
-- * (39): HG against the box white on wire 1.  X on wire 1 passes HG
--   ((207) under the lower swap); HG passes the box ((338) with x = y on
--   four wires), the box being °box₃ • P₁₃ CZ ((170′)), °box₃ passing by
--   (194) and P₁₃ CZ, which is U CZ under the swap of the wires 2 3, by
--   °CZ₂₁-ΛH₀₁ and Z on the box wire ((155) between P ⊗ P).
-- * (40): Canon40's chain.  ZX₃ is CH₂ K CH₂ K ((215)), K and its colour
--   white on wire 0 merge into B₂ = P₁₃ CZ (Canon4's merge), which passes
--   CH₂; and D = CH₂ • HG is HG white on wire 3 ((171′) under the swaps),
--   which passes K ((185)) and B₂ (°CZ₂₁-ΛH₀₁ under X on wire 2 and the
--   swap of the wires 2 3), hence the box white on wire 0.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Cores
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; X² ; Ex² ; CH²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₁₂ ; module S₂₃ ; L-sem ; U-sem ; U ; O ; O-L ; U-S₂₃ ; O-S₂₃ ; P₀₃ ; P₁₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃ using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq155 ; eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq167 ; eq170′ ; eq171′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃ using (eq185)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq194 ; °CZ₂₁-ΛH₀₁ ; S₂₃-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (S₂₃-ΛH₀₁ ; S₂₃-X₂ ; S₁₂-X₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃ using (eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (S₁₂-ZX₃)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)

open Tools (4 VRel,_===_)
open WordAlgebra (4 VRel,_===_) using (comm-•)

private
  HG : Circuit 4
  HG = Ex ↓ • ΛH 2 • Ex ↓

  Ex↑↑² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
  Ex↑↑² = lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)

  pass₂ : ∀ {a u v : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  both : ∀ {p p′ q q′ : Circuit 4} → p ≈ p′ → q ≈ q′ → p • q ≈ q • p → p′ • q′ ≈ q′ • p′
  both ep eq e = trans (sym (cong ep eq)) (trans e (cong eq ep))

  ----------------------------------------------------------------------
  -- HG against the box

  sX : S₀₁.⟪ X ⟫ ≈ X ↑
  sX = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  sZ : S₀₁.⟪ Z ⟫ ≈ Z ↑
  sZ = L-sem (Ex • Z • Ex) (Z ↑) Eq.refl

  -- X on the box wire passes HG ((207)).
  xh : X ↑ • HG ≈ HG • X ↑
  xh = S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ sX refl) (S₀₁.⟪⟫-•₂ refl sX)

  -- Z on the box wire passes HG: between P ⊗ P it is H, (155).
  module Aj = Conj {4} (PP ↓) (L-sem (PP • PP) ε Eq.refl)

  zh : Z ↓ • ΛH 2 ≈ ΛH 2 • Z ↓
  zh = Aj.⟪⟫-≈ eq155 (Aj.⟪⟫-•₂ ah refl) (Aj.⟪⟫-•₂ refl ah)
    where
    ah : Aj.⟪ H ↓ ⟫ ≈ Z ↓
    ah = L-sem (PP • H • PP) Z Eq.refl

  z↑h : Z ↑ • HG ≈ HG • Z ↑
  z↑h = S₀₁.⟪⟫-≈ zh (S₀₁.⟪⟫-•₂ sZ refl) (S₀₁.⟪⟫-•₂ refl sZ)

  -- HG passes the CZ of the wires 1 3.
  uCZ : U CZ ≈ U °CZ • Z ↑
  uCZ = U-sem CZ (°CZ • Z) Eq.refl

  h-uCZ : HG • U CZ ≈ U CZ • HG
  h-uCZ = trans (back _ uCZ) (trans (comm-• (sym °CZ₂₁-ΛH₀₁) (sym z↑h)) (front _ (sym uCZ)))

  h-P : HG • P₁₃ CZ ≈ P₁₃ CZ • HG
  h-P = S₂₃.⟪⟫-≈ h-uCZ (S₂₃.⟪⟫-•₂ S₂₃-ΛH₀₁ (U-S₂₃ CZ)) (S₂₃.⟪⟫-•₂ (U-S₂₃ CZ) S₂₃-ΛH₀₁)

  -- The box is its colour white on wire 2 times P₁₃ CZ ((170′)).
  B-form : box₃ ≈ °box₃ • P₁₃ CZ
  B-form = trans (sym left-unit) (trans (front _ (sym ob²)) (trans assoc (back _ eq170′)))
    where
    ob² : °box₃ • °box₃ ≈ ε
    ob² = N₂.⟪⟫-invol eq166

  -- (338) with x = y on four wires.
  h-box : HG • box₃ ≈ box₃ • HG
  h-box = trans (back _ B-form) (trans (comm-• eq194 h-P) (front _ (sym B-form)))

-- (338) with x = y on four wires, and HG against the CZ of the wires 1
-- 3, for the cores of (43) and (44).
HG-box₃ : (Ex ↓ • ΛH 2 • Ex ↓) • box₃ ≈ box₃ • (Ex ↓ • ΛH 2 • Ex ↓)
HG-box₃ = h-box

HG-P₁₃CZ : (Ex ↓ • ΛH 2 • Ex ↓) • P₁₃ CZ ≈ P₁₃ CZ • (Ex ↓ • ΛH 2 • Ex ↓)
HG-P₁₃CZ = h-P

------------------------------------------------------------------------
-- (39)

core39₁ : (Ex ↓ • ΛH 2 • Ex ↓) • (X ↑ • Λ□ 3 • X ↑) ≈ (X ↑ • Λ□ 3 • X ↑) • (Ex ↓ • ΛH 2 • Ex ↓)
core39₁ = comm-• (sym xh) (comm-• h-box (sym xh))

------------------------------------------------------------------------
-- (40)

private
  Λ B K Bt CH₂ D B₂ : Circuit 4
  Λ   = Λ□ 3
  B   = Ex ↓ • Λ • Ex ↓
  K   = S₁₂.⟪ B ⟫
  Bt  = X • K • X
  CH₂ = S₁₂.⟪ CH ⟫
  D   = CH₂ • HG
  B₂  = S₁₂.⟪ Λ□ 2 ↑ ⟫

  K² : K • K ≈ ε
  K² = S₁₂.⟪⟫-invol (S₀₁.⟪⟫-invol eq166)

  CH₂² : CH₂ • CH₂ ≈ ε
  CH₂² = S₁₂.⟪⟫-invol CH²

  HG² : HG • HG ≈ ε
  HG² = S₀₁.⟪⟫-invol eq167

  -- (353) at four wires: (215).
  ZX-K : ΛZX 3 ≈ CH₂ • K • CH₂ • K
  ZX-K = trans (sym S₁₂-ZX₃) (S₁₂.⟪⟫-•₄ refl refl refl refl)

  -- The merge on wire 0, through the two swaps.
  S01X : S₀₁.⟪ X ↑ ⟫ ≈ X
  S01X = conj-sym Ex² (X-step 0 (s≤s z≤n))

  S12X : S₁₂.⟪ X ⟫ ≈ X
  S12X = trans (sym assoc) (trans (front _ (sym (X-↑ Ex))) (trans assoc (trans (back _ (lemma-cong↑ (Ex • Ex) ε Ex²)) right-unit)))

  Xs : Bt ≈ S₁₂.⟪ S₀₁.⟪ X ↑ • Λ • X ↑ ⟫ ⟫
  Xs = trans (sym (S₁₂.⟪⟫-•₃ S12X refl S12X)) (S₁₂.⟪⟫-cong (sym (S₀₁.⟪⟫-•₃ S01X refl S01X)))

  merge₀ : K • Bt ≈ B₂
  merge₀ = begin
    K • Bt
      ≈⟨ back _ Xs ⟩
    S₁₂.⟪ S₀₁.⟪ Λ ⟫ ⟫ • S₁₂.⟪ S₀₁.⟪ X ↑ • Λ • X ↑ ⟫ ⟫
      ≈⟨ sym (trans (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-• Λ (X ↑ • Λ • X ↑))) (S₁₂.⟪⟫-• (S₀₁.⟪ Λ ⟫) (S₀₁.⟪ X ↑ • Λ • X ↑ ⟫))) ⟩
    S₁₂.⟪ S₀₁.⟪ Λ • (X ↑ • Λ • X ↑) ⟫ ⟫
      ≈⟨ S₁₂.⟪⟫-cong (S₀₁.⟪⟫-cong (Canon.merge canon4)) ⟩
    S₁₂.⟪ S₀₁.⟪ Λ□ 2 ↑ ⟫ ⟫
      ≈⟨ S₁₂.⟪⟫-cong (Canon.wire274 canon4) ⟩
    B₂ ∎

  -- The CZ of the wires 2 3 passes the CH of the wires 0 1.
  B₂-CH₂ : B₂ • CH₂ ≈ CH₂ • B₂
  B₂-CH₂ = S₁₂.⟪⟫-≈ (sym (low-comm CH CZ)) (S₁₂.⟪⟫-• (Λ□ 2 ↑) CH) (S₁₂.⟪⟫-• CH (Λ□ 2 ↑))

  -- CH₂ is HG merged over the colours of wire 3: (171′) under the
  -- swaps.
  s01 : S₀₁.⟪ N₂.⟪ ΛH 2 ⟫ ⟫ ≈ N₂.⟪ HG ⟫
  s01 = conj-swap (low-comm Ex X) (ΛH 2)

  s23 : S₂₃.⟪ N₂.⟪ HG ⟫ ⟫ ≈ N₃.⟪ HG ⟫
  s23 = S₂₃.⟪⟫-•₃ S₂₃-X₂ S₂₃-ΛH₀₁ S₂₃-X₂

  CH₂-form : N₃.⟪ HG ⟫ • HG ≈ CH₂
  CH₂-form = trans (S₂₃.⟪⟫-≈ step₁ (S₂₃.⟪⟫-•₂ s23 S₂₃-ΛH₀₁) (conj-sym Ex↑↑² (O-S₂₃ CH))) (sym (O-L CH))
    where
    step₁ : N₂.⟪ HG ⟫ • HG ≈ P₀₃ CH
    step₁ = S₀₁.⟪⟫-≈ eq171′ (S₀₁.⟪⟫-•₂ s01 refl) refl

  D-form : D ≈ N₃.⟪ HG ⟫
  D-form = trans (front _ (sym CH₂-form)) (trans assoc (trans (back _ HG²) right-unit))

  Bt-form : Bt ≈ K • B₂
  Bt-form = trans (sym (trans (sym assoc) (trans (front _ K²) left-unit))) (back _ merge₀)

  -- HG white on wire 3 passes K ((185)) and B₂.
  H3-K : N₃.⟪ HG ⟫ • K ≈ K • N₃.⟪ HG ⟫
  H3-K = sym (both eK eH eq185)
    where
    eK : S₁₂.⟪ S₂₃.⟪ Ex ↓ • box₃ • Ex ↓ ⟫ ⟫ ≈ K
    eK = S₁₂.⟪⟫-cong S₂₃-box₃′
    eH : S₁₂.⟪ S₂₃.⟪ N₂.⟪ S₂₃.⟪ S₁₂.⟪ HG ⟫ ⟫ ⟫ ⟫ ⟫ ≈ N₃.⟪ HG ⟫
    eH = trans (S₁₂.⟪⟫-cong (trans (S₂₃.⟪⟫-•₃ S₂₃-X₂ refl S₂₃-X₂) (N₃.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ (S₁₂.⟪ HG ⟫)))))
               (trans (S₁₂.⟪⟫-•₃ S₁₂-X₃ refl S₁₂-X₃) (N₃.⟪⟫-cong (S₁₂.⟪⟫-⟪⟫ HG)))

  H3-B₂ : N₃.⟪ HG ⟫ • B₂ ≈ B₂ • N₃.⟪ HG ⟫
  H3-B₂ = sym (S₂₃.⟪⟫-≈ e₁ (S₂₃.⟪⟫-•₂ (U-S₂₃ CZ) s23) (S₂₃.⟪⟫-•₂ s23 (U-S₂₃ CZ)))
    where
    nU : N₂.⟪ U °CZ ⟫ ≈ U CZ
    nU = U-sem (X ↑ • °CZ • X ↑) CZ Eq.refl
    e₁ : U CZ • N₂.⟪ HG ⟫ ≈ N₂.⟪ HG ⟫ • U CZ
    e₁ = N₂.⟪⟫-≈ °CZ₂₁-ΛH₀₁ (N₂.⟪⟫-•₂ nU refl) (N₂.⟪⟫-•₂ refl nU)

  Bt-D : Bt • D ≈ D • Bt
  Bt-D = trans (cong Bt-form D-form) (trans (sym (pass₂ H3-K H3-B₂)) (cong (sym D-form) (sym Bt-form)))

  H-CD : HG ≈ CH₂ • D
  H-CD = sym (trans (sym assoc) (trans (front _ CH₂²) left-unit))

  eq40c : HG • Bt ≈ ΛZX 3 • Bt • HG
  eq40c = sym (begin
    ΛZX 3 • Bt • HG
      ≈⟨ cong ZX-K (back _ H-CD) ⟩
    (CH₂ • K • CH₂ • K) • Bt • (CH₂ • D)
      ≈⟨ by-passoc ((□ • □ • □ • □) • □ • (□ • □)) (□ • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
    CH₂ • K • CH₂ • (K • Bt) • CH₂ • D
      ≈⟨ back _ (back _ (back _ (front _ merge₀))) ⟩
    CH₂ • K • CH₂ • B₂ • CH₂ • D
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (front _ B₂-CH₂)))) ⟩
    CH₂ • K • CH₂ • (CH₂ • B₂) • D
      ≈⟨ back _ (back _ (trans (sym assoc) (front _ (trans (sym assoc) (trans (front _ CH₂²) left-unit))))) ⟩
    CH₂ • K • B₂ • D
      ≈⟨ back _ (back _ (front _ (sym merge₀))) ⟩
    CH₂ • K • (K • Bt) • D
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (trans (sym assoc) (trans (front _ K²) left-unit))) refl)) ⟩
    CH₂ • Bt • D
      ≈⟨ back _ Bt-D ⟩
    CH₂ • D • Bt
      ≈⟨ trans (sym assoc) (front _ (sym H-CD)) ⟩
    HG • Bt ∎)

  -- In the spelling of the decoding: X on the wires 0 and 2 around K.
  Btd : Circuit 4
  Btd = (X • X ↑ ↑) • K • (X • X ↑ ↑)

  Btd-Bt : Btd ≈ Bt
  Btd-Bt = begin
    (X • X ↑ ↑) • K • (X • X ↑ ↑)     ≈⟨ back _ (back _ (X-↑ (X ↑))) ⟩
    (X • X ↑ ↑) • K • (X ↑ ↑ • X)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X • (X ↑ ↑ • K • X ↑ ↑) • X       ≈⟨ mid _ _ X₂K ⟩
    Bt ∎
    where
    S01X0 : S₀₁.⟪ X ⟫ ≈ X ↑
    S01X0 = X-step 0 (s≤s z≤n)
    S12X1 : S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
    S12X1 = X-step 1 (s≤s (s≤s z≤n))
    XΛX : X • Λ • X ≈ Λ
    XΛX = trans (sym assoc) (trans (front _ (Canon.x-box canon4)) (trans assoc (trans (back _ X²) right-unit)))
    X₂K : X ↑ ↑ • K • X ↑ ↑ ≈ K
    X₂K = trans (sym (S₁₂.⟪⟫-•₃ S12X1 refl S12X1))
                (S₁₂.⟪⟫-cong (trans (sym (S₀₁.⟪⟫-•₃ S01X0 refl S01X0)) (S₀₁.⟪⟫-cong XΛX)))

core40₁ : (Ex ↓ • ΛH 2 • Ex ↓) • ((X • X ↑ ↑) • (Ex ↑ • (Ex ↓ • Λ□ 3 • Ex ↓) • Ex ↑) • (X • X ↑ ↑))
          ≈ ΛZX 3 • ((X • X ↑ ↑) • (Ex ↑ • (Ex ↓ • Λ□ 3 • Ex ↓) • Ex ↑) • (X • X ↑ ↑)) • (Ex ↓ • ΛH 2 • Ex ↓)
core40₁ = trans (back _ Btd-Bt) (trans eq40c (sym (back _ (front _ Btd-Bt))))
