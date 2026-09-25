------------------------------------------------------------------------
-- Presentations of groups
--
-- A rotation between P ⊗ P against a box with wire 3 idle, of the other
-- colour on wire 2 (Clément, Lemma D.12, Equations (322) and (323))
--
-- At width 4 + j: the triply controlled ZX on wire 0 between P ⊗ P on
-- the wires 0 1, black on the wires 1 2 and of either colour on wire 3
-- (`Aᴾ α true true`, FourQubit.PForms), commutes with the box with
-- wire 3 idle, white on wire 2, black on the other of the wires 0 1 and
-- coloured x on the top wires, its box wire on wire 0 or on wire 1
-- (`Gd`, the two cases by `Vb`).  Semantically the rotation acts only
-- where wire 2 is 1 and the box only where it is 0.
--
-- The paper's induction on the length of x: on four wires it is decided
-- (Base322; the paper cites (247), (248)).  At width 5 + j the box one
-- width down is expanded by (320) — on four wires decided too (Base338),
-- from five on GeneralN.Box320 — and placed around wire 3: its rotations
-- land on the wires 0 1 2 4 (`place3-loc`), coloured they are the
-- second gates of (267) and (268) (Colours' `norm-ZX`/`norm-K`, a white
-- control on wire 4 being X there, which the first gate does not see),
-- and its smaller box, placed twice, has the wires 3 4 idle and is the
-- statement one width down placed around wire 4 (`place-34`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Gadget322
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (zero ; suc)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (same-sem ; Evaluated)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm-≈)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (C₂₄₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ using (D₂₄₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ using (Aᴾ)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃ using (module S₃₄)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies267 complete₂ complete₃ using (eq267)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies268 complete₂ complete₃ using (eq268)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Networks using (scyc ; scyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-cong ; place-low ; low-comm ; cyc ; cyc⁻¹ ; cyc⁻¹-cyc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place ; placeAt-step ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp ; below-suc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box320 complete₂ complete₃ using (eq320)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃
  using (col ; module Col ; col-place ; norm-ZX ; norm-K)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; Vb)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base338 using (W320 ; d320)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base322 using (AᴾF ; P322 ; d322)

------------------------------------------------------------------------
-- The letters of (320) at width 4 + j, and their products

data L : Set where
  zx xz kb kb′ bb : L

lt : ∀ j → L → Circuit (₄₊ j)
lt j zx  = ZX₃
lt j xz  = XZ₃
lt j kb  = S₀₁.⟪ ZX₃ ⟫
lt j kb′ = S₀₁.⟪ XZ₃ ⟫
lt j bb  = place 3 (Λ□ (₂₊ j))

-- The letters of (320), in order.
es : List L
es = zx ∷ kb ∷ bb ∷ kb′ ∷ xz ∷ kb ∷ bb ∷ kb′ ∷ []

word : ∀ {n} → (L → Circuit n) → List L → Circuit n
word f []       = ε
word f (l ∷ ls) = f l • word f ls

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  pass : ∀ {a u v : Circuit n} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  pass-word : ∀ {y : Circuit n} f ls → (∀ l → y • f l ≈ f l • y) → y • word f ls ≈ word f ls • y
  pass-word f []       e = trans right-unit (sym left-unit)
  pass-word f (l ∷ ls) e = pass (e l) (pass-word f ls e)

  -- Passing is invariant under ≈ of the passed word.
  via : ∀ {y u w : Circuit n} → u ≈ w → y • w ≈ w • y → y • u ≈ u • y
  via e p = trans (back _ e) (trans p (front _ (sym e)))

  -- If c is an involution passing y, y passes c g c as soon as it passes g.
  conj-pass : ∀ {c y g : Circuit n} → c • c ≈ ε → c • y ≈ y • c → y • g ≈ g • y →
              y • (c • g • c) ≈ (c • g • c) • y
  conj-pass {c} {y} {g} c² cy yg = begin
    y • c • g • c        ≈⟨ trans (sym assoc) (trans (front _ (sym cy)) assoc) ⟩
    c • y • g • c        ≈⟨ back _ (trans (sym assoc) (trans (front _ yg) assoc)) ⟩
    c • g • y • c        ≈⟨ back _ (back _ (sym cy)) ⟩
    c • g • c • y        ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (c • g • c) • y ∎

  -- A conjugation by an involution, letter by letter.
  module CW (c : Circuit n) (c² : c • c ≈ ε) where
    open Conj c c²
    ⟪⟫-word : ∀ f ls → ⟪ word f ls ⟫ ≈ word (λ l → ⟪ f l ⟫) ls
    ⟪⟫-word f []       = ⟪⟫-ε
    ⟪⟫-word f (l ∷ ls) = trans (⟪⟫-• (f l) (word f ls)) (back _ (⟪⟫-word f ls))

------------------------------------------------------------------------
-- Placement around wire 3

module _ {r : ℕ} where
  open Tools ((₄₊ r) VRel,_===_)

  place-ε : place {r = r} 3 ε ≈ ε
  place-ε = trans (back _ left-unit) (cyc⁻¹-cyc 3)

  place-word : ∀ (f : L → Circuit (₃₊ r)) ls → place 3 (word f ls) ≈ word (λ l → place 3 (f l)) ls
  place-word f []       = place-ε
  place-word f (l ∷ ls) = trans (place-• 3 (f l) (word f ls)) (back _ (place-word f ls))

  -- The swap of the wires 0 1 goes inside.
  S-place : ∀ (V : Circuit (₃₊ r)) → Ex ↓ • place 3 V • Ex ↓ ≈ place 3 (Ex ↓ • V • Ex ↓)
  S-place V = sym (trans (place-• 3 (Ex ↓) (V • Ex ↓))
                (cong (place-low 3 (Ex {1})) (trans (place-• 3 V (Ex ↓)) (back _ (place-low 3 (Ex {1}))))))

module _ {j : ℕ} where
  open Tools ((₁₊ (₄₊ j)) VRel,_===_)

  private
    module Sw = Conj {₁₊ (₄₊ j)} (swapAt 3) (swapAt² 3)

    ≡→≈ : ∀ {p q : Circuit (₁₊ (₄₊ j))} → p ≡ q → p ≈ q
    ≡→≈ Eq.refl = refl

  -- A four-wire circuit placed around wire 3 is the circuit with its
  -- wire 3 moved up to wire 4.
  place3-loc : ∀ (c : Circuit 4) → place 3 (c ↓ᵏ j) ≈ Ex ↑ ↑ ↑ • (top c ↓ᵏ j) • Ex ↑ ↑ ↑
  place3-loc c = begin
    place 3 (c ↓ᵏ j)                   ≈⟨ ≡→≈ (Eq.sym (placeAt-place 3 (c ↓ᵏ j))) ⟩
    placeAt 3 (c ↓ᵏ j)                 ≈⟨ sym (Sw.⟪⟫-⟪⟫ _) ⟩
    Sw.⟪ Sw.⟪ placeAt 3 (c ↓ᵏ j) ⟫ ⟫   ≈⟨ Sw.⟪⟫-cong (sym (placeAt-step 3 (c ↓ᵏ j) (s≤s (s≤s (s≤s (s≤s z≤n)))))) ⟩
    Sw.⟪ placeAt 4 (c ↓ᵏ j) ⟫          ≈⟨ Sw.⟪⟫-cong (≡→≈ (placeAt-place 4 (c ↓ᵏ j))) ⟩
    Sw.⟪ place 4 (c ↓ᵏ j) ⟫            ≈⟨ Sw.⟪⟫-cong (place-low 4 c) ⟩
    Sw.⟪ top c ↓ᵏ j ⟫ ∎

  -- A colouring through the swap of the wires 3 4.
  col-S₃₄ : ∀ (t : Bits (₁₊ (₄₊ j))) w → S₃₄.⟪ col t w ⟫ ≈ col (swB 3 t) (S₃₄.⟪ w ⟫)
  col-S₃₄ t w = S₃₄.⟪⟫-•₃ (swapAt-negsB 3 t) refl (swapAt-negsB 3 t)

  X₄² : X ↑ ↑ ↑ ↑ • X ↑ ↑ ↑ ↑ ≈ ε
  X₄² = lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)))

  -- The swap of the wires 3 4 carries X on wire 3 to wire 4.
  S-X₃ : S₃₄.⟪ X ↑ ↑ ↑ ⟫ ≈ X ↑ ↑ ↑ ↑
  S-X₃ = X-step 3 (s≤s (s≤s (s≤s (s≤s z≤n))))

  -- X on wire 4 passes the first gate.
  X₄-A : ∀ α → X ↑ ↑ ↑ ↑ • Aᴾ α true true ≈ Aᴾ α true true • X ↑ ↑ ↑ ↑
  X₄-A true  = sym (local-comm (Aᴾ {0} true true true) X)
  X₄-A false = sym (local-comm (Aᴾ {0} false true true) X)

  -- The first gate one width down, placed around wire 4.
  place4-A : ∀ α → place 4 (Aᴾ {j} α true true) ≈ Aᴾ α true true
  place4-A true  = place-low 4 (Aᴾ {0} true true true)
  place4-A false = place-low 4 (Aᴾ {0} false true true)

  lift4 : ∀ α {u : Circuit (₄₊ j)} → (₄₊ j) ⊢ Aᴾ α true true • u ≈ u • Aᴾ α true true →
          Aᴾ α true true • place 4 u ≈ place 4 u • Aᴾ α true true
  lift4 α {u} e = begin
    Aᴾ α true true • place 4 u           ≈⟨ front _ (sym (place4-A α)) ⟩
    place 4 A₀ • place 4 u               ≈⟨ sym (place-• 4 A₀ u) ⟩
    place 4 (A₀ • u)                     ≈⟨ place-cong 4 e ⟩
    place 4 (u • A₀)                     ≈⟨ place-• 4 u A₀ ⟩
    place 4 u • place 4 A₀               ≈⟨ back _ (place4-A α) ⟩
    place 4 u • Aᴾ α true true ∎
    where
    A₀ : Circuit (₄₊ j)
    A₀ = Aᴾ α true true

  -- A second gate negated on wire 3, under the swap of the wires 3 4:
  -- X on wire 4, which passes the first gate.
  neg₃ : ∀ α {G : Circuit (₁₊ (₄₊ j))} → Aᴾ α true true • S₃₄.⟪ G ⟫ ≈ S₃₄.⟪ G ⟫ • Aᴾ α true true →
         Aᴾ α true true • S₃₄.⟪ X ↑ ↑ ↑ • G • X ↑ ↑ ↑ ⟫ ≈ S₃₄.⟪ X ↑ ↑ ↑ • G • X ↑ ↑ ↑ ⟫ • Aᴾ α true true
  neg₃ α e = via (S₃₄.⟪⟫-•₃ S-X₃ refl S-X₃) (conj-pass X₄² (X₄-A α) e)

-- Two idle wires 3 4, placed in either order: the two networks differ
-- by the swap of the wires 0 1 inside, which passes the circuit lifted
-- two wires (as Idle's place-swap one wire lower).
module _ {r : ℕ} (z : Circuit (₃₊ r)) where

  private
    open Tools ((₁₊ (₄₊ r)) VRel,_===_)

    N≈ : cyc⁻¹ 4 • cyc⁻¹ 3 ↑ ≈ (cyc⁻¹ 3 • cyc⁻¹ 3 ↑) • Ex ↓
    N≈ = perm-≈ {u = scyc⁻¹ 4 • (scyc⁻¹ 3) S.↑} {v = (scyc⁻¹ 3 • (scyc⁻¹ 3) S.↑) • S.σ}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc zero)))) → Eq.refl
              ; (suc (suc (suc (suc (suc _))))) → Eq.refl })

    M≈ : cyc 3 ↑ • cyc 4 ≈ Ex ↓ • (cyc 3 ↑ • cyc 3)
    M≈ = perm-≈ {u = (scyc 3) S.↑ • scyc 4} {v = S.σ • ((scyc 3) S.↑ • scyc 3)}
           (λ { zero → Eq.refl ; (suc zero) → Eq.refl ; (suc (suc zero)) → Eq.refl
              ; (suc (suc (suc zero))) → Eq.refl ; (suc (suc (suc (suc zero)))) → Eq.refl
              ; (suc (suc (suc (suc (suc _))))) → Eq.refl })

  place-34 : place 3 (place 3 z) ≈ place 4 (place 3 z)
  place-34 = begin
    cyc⁻¹ 3 • (cyc⁻¹ 3 ↑ • z ↑ ↑ • cyc 3 ↑) • cyc 3
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (cyc⁻¹ 3 • cyc⁻¹ 3 ↑) • z ↑ ↑ • (cyc 3 ↑ • cyc 3)
      ≈⟨ back _ (back _ (sym (trans (front _ Ex²) left-unit))) ⟩
    (cyc⁻¹ 3 • cyc⁻¹ 3 ↑) • z ↑ ↑ • ((Ex ↓ • Ex ↓) • cyc 3 ↑ • cyc 3)
      ≈⟨ by-passoc ((□ • □) • □ • ((□ • □) • □ • □)) ((□ • □) • □ • □ • (□ • □ • □)) Eq.refl ⟩
    (cyc⁻¹ 3 • cyc⁻¹ 3 ↑) • z ↑ ↑ • Ex ↓ • (Ex ↓ • cyc 3 ↑ • cyc 3)
      ≈⟨ back _ (trans (sym assoc) (front _ (sym (low-comm Ex z)))) ⟩
    (cyc⁻¹ 3 • cyc⁻¹ 3 ↑) • (Ex ↓ • z ↑ ↑) • (Ex ↓ • cyc 3 ↑ • cyc 3)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □ • □)) (((□ • □) • □) • □ • (□ • (□ • □))) Eq.refl ⟩
    ((cyc⁻¹ 3 • cyc⁻¹ 3 ↑) • Ex ↓) • z ↑ ↑ • (Ex ↓ • (cyc 3 ↑ • cyc 3))
      ≈⟨ cong (sym N≈) (back _ (sym M≈)) ⟩
    (cyc⁻¹ 4 • cyc⁻¹ 3 ↑) • z ↑ ↑ • (cyc 3 ↑ • cyc 4)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    cyc⁻¹ 4 • (cyc⁻¹ 3 ↑ • z ↑ ↑ • cyc 3 ↑) • cyc 4 ∎

------------------------------------------------------------------------
-- (320) at width 4 + j

E320 : Comp 4 → ∀ j → Below (₄₊ j) → (₄₊ j) ⊢ Λ□ (₃₊ j) ≈ word (lt j) es
E320 c₄ zero    _ = c₄ (same-sem (Λ□ 3) W320 (Evaluated.same d320))
E320 c₄ (suc j) b = begin
  Λ□ (₄₊ j)
    ≈⟨ eq320 j b ⟩
  ZX₃ • (S₀₁.⟪ ZX₃ ⟫ • place 3 (Λ□ (₃₊ j)) • S₀₁.⟪ XZ₃ ⟫) • XZ₃ • (S₀₁.⟪ ZX₃ ⟫ • place 3 (Λ□ (₃₊ j)) • S₀₁.⟪ XZ₃ ⟫)
    ≈⟨ by-passoc (□ • (□ • □ • □) • □ • (□ • □ • □)) (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl ⟩
  ZX₃ • S₀₁.⟪ ZX₃ ⟫ • place 3 (Λ□ (₃₊ j)) • S₀₁.⟪ XZ₃ ⟫ • XZ₃ • S₀₁.⟪ ZX₃ ⟫ • place 3 (Λ□ (₃₊ j)) • S₀₁.⟪ XZ₃ ⟫
    ≈⟨ back _ (back _ (back _ (back _ (back _ (back _ (back _ (sym right-unit))))))) ⟩
  word (lt (suc j)) es ∎
  where open Tools ((₄₊ (suc j)) VRel,_===_)

-- The letters of the box on wire 0 or on wire 1.
lv : ∀ j → Bool → L → Circuit (₄₊ j)
lv j true  l = lt j l
lv j false l = S₀₁.⟪ lt j l ⟫

Vb-word : Comp 4 → ∀ j → Below (₄₊ j) → ∀ v → (₄₊ j) ⊢ Vb v (suc j) ≈ word (lv j v) es
Vb-word c₄ j b true  = E320 c₄ j b
Vb-word c₄ j b false = trans (S₀₁.⟪⟫-cong (E320 c₄ j b)) (CW.⟪⟫-word (Ex ↓) Ex² (lt j) es)
  where open Tools ((₄₊ j) VRel,_===_)

------------------------------------------------------------------------
-- The statement

Gd : ℕ → Set
Gd j = ∀ (α : Bool) (x : Bits j) (v : Bool) →
       (₄₊ j) ⊢ Aᴾ α true true • place 3 (col (true ∷ true ∷ false ∷ x) (Vb v j))
              ≈ place 3 (col (true ∷ true ∷ false ∷ x) (Vb v j)) • Aᴾ α true true

-- On four wires, decided.
gd₀ : Comp 4 → Gd 0
gd₀ c₄ true  [] v = c₄ (same-sem (AᴾF true • P322 v) (P322 v • AᴾF true) (Evaluated.same (d322 true v)))
gd₀ c₄ false [] v = c₄ (same-sem (AᴾF false • P322 v) (P322 v • AᴾF false) (Evaluated.same (d322 false v)))

------------------------------------------------------------------------
-- The step, at width 5 + j

-- Inverse letters stay inverse when coloured.
module _ {j : ℕ} where
  open Tools ((₄₊ j) VRel,_===_)

  col-inv : ∀ (s : Bits (₄₊ j)) {w w′ : Circuit (₄₊ j)} → w • w′ ≈ ε → col s w • col s w′ ≈ ε
  col-inv s {w} {w′} e = trans (sym (Col.⟪⟫-• s w w′)) (trans (Col.⟪⟫-cong s e) (Col.⟪⟫-ε s))

  ZX-XZ : ZX₃ • XZ₃ ≈ ε
  ZX-XZ = eq208′
  XZ-ZX : XZ₃ • ZX₃ ≈ ε
  XZ-ZX = eq208
  K-K′ : S₀₁.⟪ ZX₃ ⟫ • S₀₁.⟪ XZ₃ ⟫ ≈ ε
  K-K′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)
  K′-K : S₀₁.⟪ XZ₃ ⟫ • S₀₁.⟪ ZX₃ ⟫ ≈ ε
  K′-K = trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε)

module Step (j : ℕ) (ih : Gd j) (α : Bool) (x₄ : Bool) (x′ : Bits j) where

  private
    open Tools ((₁₊ (₄₊ j)) VRel,_===_)
    open WordAlgebra ((₁₊ (₄₊ j)) VRel,_===_) using (comm-inv)

    A : Circuit (₁₊ (₄₊ j))
    A = Aᴾ α true true

    s : Bits (₄₊ j)
    s = true ∷ true ∷ false ∷ x₄ ∷ x′

  -- A letter coloured and placed.
  pc : Circuit (₄₊ j) → Circuit (₁₊ (₄₊ j))
  pc w = place 3 (col s w)

  private
    pc-cong : ∀ {w w′} → (₄₊ j) ⊢ w ≈ w′ → pc w ≈ pc w′
    pc-cong e = place-cong 3 (Col.⟪⟫-cong s e)

    pc-inv : ∀ {w w′} → (₄₊ j) ⊢ w • w′ ≈ ε → pc w • pc w′ ≈ ε
    pc-inv {w} {w′} e = trans (sym (place-• 3 (col s w) (col s w′))) (trans (place-cong 3 (col-inv s e)) place-ε)

    -- A passes the inverse of what it passes.
    inv : ∀ {w w′} → (₄₊ j) ⊢ w • w′ ≈ ε → (₄₊ j) ⊢ w′ • w ≈ ε → A • pc w ≈ pc w • A → A • pc w′ ≈ pc w′ • A
    inv e e′ p = comm-inv (pc-inv e) (pc-inv e′) p

    t : Bits (₁₊ (₄₊ j))
    t = true ∷ true ∷ false ∷ x₄ ∷ true ∷ x′

    -- The rotations, placed: the second gates of (268) and (267) under
    -- the swap of the wires 3 4.
    pc-Z : pc ZX₃ ≈ S₃₄.⟪ C₂₄₁ x₄ true true ⟫
    pc-Z = begin
      place 3 (col s ZX₃)                              ≈⟨ sym (col-place true true false true (x₄ ∷ x′) ZX₃) ⟩
      col (swB 3 t) (place 3 ZX₃)                      ≈⟨ Col.⟪⟫-cong (swB 3 t) (place3-loc (ΛZX 3)) ⟩
      col (swB 3 t) (S₃₄.⟪ ZX₃ ⟫)                      ≈⟨ sym (col-S₃₄ t ZX₃) ⟩
      S₃₄.⟪ col t ZX₃ ⟫                                ≈⟨ S₃₄.⟪⟫-cong (norm-ZX true true x₄ (true ∷ x′)) ⟩
      S₃₄.⟪ C₂₄₁ x₄ true true ⟫ ∎

    pc-K : pc (S₀₁.⟪ ZX₃ ⟫) ≈ S₃₄.⟪ D₂₄₀ x₄ true true ⟫
    pc-K = begin
      place 3 (col s (S₀₁.⟪ ZX₃ ⟫))                    ≈⟨ sym (col-place true true false true (x₄ ∷ x′) (S₀₁.⟪ ZX₃ ⟫)) ⟩
      col (swB 3 t) (place 3 (S₀₁.⟪ ZX₃ ⟫))            ≈⟨ Col.⟪⟫-cong (swB 3 t) (place3-loc (Ex • ΛZX 3 • Ex)) ⟩
      col (swB 3 t) (S₃₄.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫)              ≈⟨ sym (col-S₃₄ t (S₀₁.⟪ ZX₃ ⟫)) ⟩
      S₃₄.⟪ col t (S₀₁.⟪ ZX₃ ⟫) ⟫                      ≈⟨ S₃₄.⟪⟫-cong (norm-K true true x₄ (true ∷ x′)) ⟩
      S₃₄.⟪ D₂₄₀ x₄ true true ⟫ ∎

    fam268 : ∀ γ → A • S₃₄.⟪ C₂₄₁ γ true true ⟫ ≈ S₃₄.⟪ C₂₄₁ γ true true ⟫ • A
    fam268 true  = eq268 α true true true true
    fam268 false = neg₃ α (eq268 α true true true true)

    fam267 : ∀ γ → A • S₃₄.⟪ D₂₄₀ γ true true ⟫ ≈ S₃₄.⟪ D₂₄₀ γ true true ⟫ • A
    fam267 true  = eq267 α true true true true
    fam267 false = neg₃ α (eq267 α true true true true)

    rZ : A • pc ZX₃ ≈ pc ZX₃ • A
    rZ = via pc-Z (fam268 x₄)

    rK : A • pc (S₀₁.⟪ ZX₃ ⟫) ≈ pc (S₀₁.⟪ ZX₃ ⟫) • A
    rK = via pc-K (fam267 x₄)

    -- The smaller box, placed twice: the statement one width down.
    rB : ∀ v → A • pc (place 3 (Vb v j)) ≈ pc (place 3 (Vb v j)) • A
    rB v = via (trans (place-cong 3 (col-place true true false x₄ x′ (Vb v j))) (place-34 _))
               (lift4 α (ih α x′ v))

    SS : ∀ w → (₄₊ j) ⊢ S₀₁.⟪ S₀₁.⟪ w ⟫ ⟫ ≈ w
    SS w = S₀₁.⟪⟫-⟪⟫ w

  letter : ∀ v l → A • pc (lv j v l) ≈ pc (lv j v l) • A
  letter true  zx  = rZ
  letter true  kb  = rK
  letter true  xz  = inv ZX-XZ XZ-ZX rZ
  letter true  kb′ = inv K-K′ K′-K rK
  letter true  bb  = rB true
  letter false zx  = rK
  letter false kb  = via (pc-cong (SS ZX₃)) rZ
  letter false xz  = inv K-K′ K′-K rK
  letter false kb′ = via (pc-cong (SS XZ₃)) (inv ZX-XZ XZ-ZX rZ)
  letter false bb  = via (pc-cong (S-place (Λ□ (₂₊ j)))) (rB false)

------------------------------------------------------------------------
-- At every width

gd : Comp 4 → ∀ j → Below (₄₊ j) → Gd j
gd c₄ zero    _ = gd₀ c₄
gd c₄ (suc j) b α (x₄ ∷ x′) v =
  via (trans (place-cong 3 (Col.⟪⟫-cong s (Vb-word c₄ j b′ v)))
             (trans (place-cong 3 (CW.⟪⟫-word (negsB s) (negs² s) (lv j v) es))
                    (place-word (λ l → col s (lv j v l)) es)))
      (pass-word (λ l → place 3 (col s (lv j v l))) es (Step.letter j (gd c₄ j b′) α x₄ x′ v))
  where
  open Tools ((₄₊ (suc j)) VRel,_===_)
  b′ : Below (₄₊ j)
  b′ = below-suc b
  s : Bits (₄₊ j)
  s = true ∷ true ∷ false ∷ x₄ ∷ x′
