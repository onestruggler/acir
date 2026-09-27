------------------------------------------------------------------------
-- Presentations of groups
--
-- The low decoded letters of Lemma 8.8 (Clément, Appendix E.5)
--
-- At width 3 + m the Gray codes of 0 … 4 have t = toBits m 0 — all
-- white — on the wires 3 … (`g0` … `g4`), so the gates the decoding makes
-- of letters with indices among them share the negations of those
-- wires.  The layouts they are placed by (`lay0`, `lay2`, `lay3`,
-- `layH`), the negations as a conjugation (`T`, X on the wires 2 …, and
-- `CT`), and the gadget — the decoded H_[0,1] H_[3,2] — as the H gate
-- under the swap of the wires 0 1 between them (`gadget-form`).  Shared
-- by the rules (39) and (40).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Lemma88.Layout {m : ℕ} where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (zero ; suc)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X²)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (toBits ; gray ; hd)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; tgtH ; Layout ; negs ; conj₂ ; ΛH)
open import Examples.Groups.Real-Clifford+CH.Decoding
  using (gcode ; layout□ ; layoutH ; layoutHFrom ; slot ; gadget)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)

private
  N : ℕ
  N = ₃₊ m

  variable
    k : ℕ

------------------------------------------------------------------------
-- The Gray codes of 0 … 4

private
  hd-Z : ∀ j → hd (toBits j 0) ≡ false
  hd-Z zero    = Eq.refl
  hd-Z (suc j) = Eq.refl

  gray-Z : ∀ j → gray (toBits j 0) ≡ toBits j 0
  gray-Z zero    = Eq.refl
  gray-Z (suc j) = Eq.cong₂ _∷_ (hd-Z j) (gray-Z j)

t : Bits m
t = toBits m 0

g0 : gcode {m} 0 ≡ false ∷ false ∷ false ∷ t
g0 = Eq.cong₂ (λ h z → false ∷ false ∷ h ∷ z) (hd-Z m) (gray-Z m)

g1 : gcode {m} 1 ≡ true ∷ false ∷ false ∷ t
g1 = Eq.cong₂ (λ h z → true ∷ false ∷ h ∷ z) (hd-Z m) (gray-Z m)

g2 : gcode {m} 2 ≡ true ∷ true ∷ false ∷ t
g2 = Eq.cong₂ (λ h z → true ∷ true ∷ h ∷ z) (hd-Z m) (gray-Z m)

g3 : gcode {m} 3 ≡ false ∷ true ∷ false ∷ t
g3 = Eq.cong₂ (λ h z → false ∷ true ∷ h ∷ z) (hd-Z m) (gray-Z m)

g4 : gcode {m} 4 ≡ false ∷ true ∷ true ∷ t
g4 = Eq.cong₂ (λ h z → false ∷ true ∷ not h ∷ z) (hd-Z m) (gray-Z m)

g6 : gcode {m} 6 ≡ true ∷ false ∷ true ∷ t
g6 = Eq.cong₂ (λ h z → true ∷ false ∷ not h ∷ z) (hd-Z m) (gray-Z m)

g7 : gcode {m} 7 ≡ false ∷ false ∷ true ∷ t
g7 = Eq.cong₂ (λ h z → false ∷ false ∷ not h ∷ z) (hd-Z m) (gray-Z m)

------------------------------------------------------------------------
-- The layouts

-- The box for 0, 1: the target on wire 0, white controls elsewhere.
L₀ : Layout N
L₀ = tgt ∷ ctrl false ∷ ctrl false ∷ zipWith slot t t

lay0 : layout□ {m} 0 ≡ L₀
lay0 = Eq.cong₂ (zipWith slot) g0 g1

-- The gate for 2, 3: the target on wire 0, black on wire 1.
L₂ : Layout N
L₂ = tgt ∷ ctrl true ∷ ctrl false ∷ zipWith slot t t

lay2 : layout□ {m} 2 ≡ L₂
lay2 = Eq.cong₂ (zipWith slot) g2 g3

-- The box for 3, 4: the target on wire 2, white on wire 0, black on 1.
L₃ : Layout N
L₃ = ctrl false ∷ ctrl true ∷ tgt ∷ zipWith slot t t

lay3 : layout□ {m} 3 ≡ L₃
lay3 = Eq.cong₂ (zipWith slot) g3 g4

-- The gadget: the H on wire 0, the box on wire 1, white controls.
LH : Layout N
LH = tgtH ∷ tgt ∷ ctrl false ∷ layoutHFrom 3 0 1 t

layH : layoutH {m} (gcode 0) 0 1 ≡ LH
layH = Eq.cong (λ g → layoutH {m} g 0 1) g0

-- On the wires 3 … every one of them has the controls of the bits of t.
negs-tail : ∀ (s : Bits k) w → negs (zipWith slot s s) ≡ negs (layoutHFrom (₃₊ w) 0 1 s)
negs-tail []          w = Eq.refl
negs-tail (true ∷ s)  w = Eq.cong _↑ (negs-tail s (suc w))
negs-tail (false ∷ s) w = Eq.cong (λ z → X • z ↑) (negs-tail s (suc w))

-- The same for the H-patterns (1 , 0) and (0 , 2).
negs-tail₁₀ : ∀ (s : Bits k) w → negs (zipWith slot s s) ≡ negs (layoutHFrom (₃₊ w) 1 0 s)
negs-tail₁₀ []          w = Eq.refl
negs-tail₁₀ (true ∷ s)  w = Eq.cong _↑ (negs-tail₁₀ s (suc w))
negs-tail₁₀ (false ∷ s) w = Eq.cong (λ z → X • z ↑) (negs-tail₁₀ s (suc w))

negs-tail₀₂ : ∀ (s : Bits k) w → negs (zipWith slot s s) ≡ negs (layoutHFrom (₃₊ w) 0 2 s)
negs-tail₀₂ []          w = Eq.refl
negs-tail₀₂ (true ∷ s)  w = Eq.cong _↑ (negs-tail₀₂ s (suc w))
negs-tail₀₂ (false ∷ s) w = Eq.cong (λ z → X • z ↑) (negs-tail₀₂ s (suc w))

-- The negations of a layout are an involution.
negs² : ∀ (L : Layout k) → k ⊢ negs L • negs L ≈ ε
negs² {k} [] = left-unit
  where open Tools (k VRel,_===_)
negs² {suc k} (ctrl false ∷ L) = begin
  (X • negs L ↑) • (X • negs L ↑)     ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  X • (negs L ↑ • X) • negs L ↑       ≈⟨ back _ (front _ (sym (X-↑ (negs L)))) ⟩
  X • (X • negs L ↑) • negs L ↑       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (X • X) • (negs L ↑ • negs L ↑)     ≈⟨ trans (front _ X²) left-unit ⟩
  negs L ↑ • negs L ↑                 ≈⟨ lemma-cong↑ (negs L • negs L) ε (negs² L) ⟩
  ε ∎
  where open Tools ((₁₊ k) VRel,_===_)
negs² {suc k} (ctrl true ∷ L) = lemma-cong↑ (negs L • negs L) ε (negs² L)
  where open Tools ((₁₊ k) VRel,_===_)
negs² {suc k} (tgt ∷ L)       = lemma-cong↑ (negs L • negs L) ε (negs² L)
  where open Tools ((₁₊ k) VRel,_===_)
negs² {suc k} (tgtH ∷ L)      = lemma-cong↑ (negs L • negs L) ε (negs² L)
  where open Tools ((₁₊ k) VRel,_===_)

------------------------------------------------------------------------
-- The common negations

open Tools (N VRel,_===_)

NY : Circuit m
NY = negs (layoutHFrom 3 0 1 t)

-- X on the wires 2 … where t is white.
T : Circuit N
T = negs LH

T² : T • T ≈ ε
T² = negs² LH

module CT = Conj T T²

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

-- The H gate under the swap of the wires 0 1.
S : Circuit N
S = Ex ↓ • ΛH (₁₊ m) • Ex ↓

-- The gadget: the H gate under the swap of the wires 0 1, between the
-- negations.
gadget-≡ : gadget {m} ≡ T • (Ex • ε) • ε • ΛH (₁₊ m) • ε • (ε • Ex) • T
gadget-≡ = Eq.cong (λ L → conj₂ L (ΛH (₁₊ m))) layH

gadget-form : gadget {m} ≈ CT.⟪ S ⟫
gadget-form = begin
  gadget                                              ≈⟨ ≡→≈ gadget-≡ ⟩
  T • (Ex • ε) • ε • ΛH (₁₊ m) • ε • (ε • Ex) • T     ≈⟨ back _ (front _ right-unit) ⟩
  T • Ex • ε • ΛH (₁₊ m) • ε • (ε • Ex) • T           ≈⟨ back _ (back _ left-unit) ⟩
  T • Ex • ΛH (₁₊ m) • ε • (ε • Ex) • T               ≈⟨ back _ (back _ (back _ left-unit)) ⟩
  T • Ex • ΛH (₁₊ m) • (ε • Ex) • T                   ≈⟨ back _ (back _ (back _ (front _ left-unit))) ⟩
  T • Ex • ΛH (₁₊ m) • Ex • T                         ≈⟨ by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  T • (Ex • ΛH (₁₊ m) • Ex) • T ∎
