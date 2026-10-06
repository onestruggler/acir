------------------------------------------------------------------------
-- Presentations of groups
--
-- The box on four qubits against its colourings, and as a squared
-- rotation (Clément, Appendix E.5 at n = 4, from Lemma D.5)
--
-- On four wires the box at the canonical position is Lemma D.5's box₃,
-- and the box on wire 1 is box₃′.
--
-- (335): a colouring white on the wires S ⊆ {1, 2, 3} of the box.
-- White on one wire c the coloured box merges with the box, in either
-- order, into D_c — CZ ↑ ↑, P₁₃ CZ, U CZ, on the wires 1–3 ((170) and
-- its relatives) — so Y_c B Y_c is D_c • B and B • D_c.  Peeling the
-- white wires one at a time (`stepQ`, `stepR`), the coloured box is Q • B
-- and B • R with Q, R on the wires 1–3, and the box passes it iff Q ≈ R,
-- a three-wire evaluation.  X on the box wire does not count.
--
-- (336): the box against the box on wire 1, white on the wires 2 3, is
-- (179), (179) under the swap of the wires 2 3, and (180); X on wires 0
-- and 1 does not count.
--
-- (355): the box is CCZX c CCXZ c with c the CZ of the wires 0 3, CCZX
-- is ZX₃ ZX₃° ((223)) and CCXZ is XZ₃° XZ₃ ((224)), ° white on wire 3;
-- ZX₃° passes c and cancels XZ₃°, and c XZ₃ c is ZX₃ ((212), (213)).
-- The XZ form by inverses.  Checked numerically first (scratchpad
-- small-widths/c335.py, t355_small.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W4.Box
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (U ; L-comm)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₀₁ ; module S₂₃ ; U₃ ; U₃-sem ; P₀₃ ; P₁₃ ; P₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀² ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq166)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃ using (°box₃ ; eq170 ; eq170′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq170₃ ; S₂₃-box₃′ ; S₂₃-°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; eq179 ; eq180)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃ using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃ using (S₀₁-N₃ ; S₁₂-N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′ ; eq212 ; eq213)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃ using (eq231)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃ using (eq223′ ; eq224)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃ using (ΛH₂′)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; B₁ ; C335 ; C336 ; col-flip ; X₁-B)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)

open Tools (4 VRel,_===_)
open WordAlgebra (4 VRel,_===_) using (comm-inv ; inv-unique)

private
  B : Circuit 4
  B = Λ□ 3

  B² : B • B ≈ ε
  B² = Canon.invol canon4

  xb : X • B ≈ B • X
  xb = Canon.x-box canon4

  pass₃ : ∀ {a u v w : Circuit 4} → a • u ≈ u • a → a • v ≈ v • a → a • w ≈ w • a →
          a • (u • v • w) ≈ (u • v • w) • a
  pass₃ eu ev ew = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _
                     (trans (sym assoc) (trans (front _ ev) (trans assoc (trans (back _ ew) (sym assoc))))))
                     (sym assoc))))

  -- An X commuting with the rest of a colouring peels off.
  peel : ∀ (x N w : Circuit 4) → x • N ≈ N • x → (x • N) • w • (x • N) ≈ x • (N • w • N) • x
  peel x N w e = trans (back _ (back _ e)) (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)

  -- A white wire 0, 1, 2 or 3 of a colouring, peeled.
  col₀ : ∀ (t : Bits 3) (w : Circuit 4) → col (false ∷ t) w ≈ X • col (true ∷ t) w • X
  col₀ t w = peel X (negsB t ↑) w (X-↑ (negsB t))

  col₁ : ∀ (t : Bits 2) (w : Circuit 4) → col (true ∷ false ∷ t) w ≈ N₁.⟪ col (true ∷ true ∷ t) w ⟫
  col₁ t w = peel (X ↑) (negsB t ↑ ↑) w (lemma-cong↑ (X • negsB t ↑) (negsB t ↑ • X) (X-↑ (negsB t)))

  col₂ : ∀ (d : Bool) (w : Circuit 4) → col (true ∷ true ∷ false ∷ d ∷ []) w ≈ N₂.⟪ col (true ∷ true ∷ true ∷ d ∷ []) w ⟫
  col₂ d w = peel (X ↑ ↑) (negsB (d ∷ []) ↑ ↑ ↑) w
                  (lemma-cong↑ (X ↑ • negsB (d ∷ []) ↑ ↑) (negsB (d ∷ []) ↑ ↑ • X ↑)
                    (lemma-cong↑ (X • negsB (d ∷ []) ↑) (negsB (d ∷ []) ↑ • X) (X-↑ (negsB (d ∷ [])))))

  col₃ : ∀ (w : Circuit 4) → col (true ∷ true ∷ true ∷ false ∷ []) w ≈ N₃.⟪ col (true ∷ true ∷ true ∷ true ∷ []) w ⟫
  col₃ w = peel (X ↑ ↑ ↑) ε w (trans right-unit (sym left-unit))

  col⊤ : ∀ (w : Circuit 4) → col (true ∷ true ∷ true ∷ true ∷ []) w ≈ w
  col⊤ w = trans left-unit right-unit

------------------------------------------------------------------------
-- (335)

private
  D₁ D₂ D₃ : Circuit 4
  D₁ = CZ ↑ ↑
  D₂ = P₁₃ CZ
  D₃ = U CZ

  -- The merges with the box white on one wire, in both orders.
  N₁-D₁ : N₁.⟪ D₁ ⟫ ≈ D₁
  N₁-D₁ = N₁.⟪⟫-fix (lemma-cong↑ (X • CZ ↑) (CZ ↑ • X) (X-↑ CZ))

  N₃-D₃ : N₃.⟪ D₃ ⟫ ≈ D₃
  N₃-D₃ = N₃.⟪⟫-fix (sym (lemma-cong↑ (CZ • X ↑ ↑) (X ↑ ↑ • CZ) (L-comm CZ X)))

  m₁ : B • N₁.⟪ B ⟫ ≈ D₁
  m₁ = Canon.merge canon4

  m₁′ : N₁.⟪ B ⟫ • B ≈ D₁
  m₁′ = N₁.⟪⟫-≈ m₁ (N₁.⟪⟫-•₂ refl (N₁.⟪⟫-⟪⟫ B)) N₁-D₁

  m₂ : B • N₂.⟪ B ⟫ ≈ D₂
  m₂ = eq170

  m₂′ : N₂.⟪ B ⟫ • B ≈ D₂
  m₂′ = eq170′

  m₃ : B • N₃.⟪ B ⟫ ≈ D₃
  m₃ = eq170₃

  m₃′ : N₃.⟪ B ⟫ • B ≈ D₃
  m₃′ = N₃.⟪⟫-≈ m₃ (N₃.⟪⟫-•₂ refl (N₃.⟪⟫-⟪⟫ B)) N₃-D₃

  -- From a merge, the coloured box as the merge times the box.
  fromL : ∀ {W D : Circuit 4} → B • W ≈ D → W ≈ B • D
  fromL {W} {D} e = trans (sym left-unit) (trans (front _ (sym B²)) (trans assoc (back _ e)))

  fromR : ∀ {W D : Circuit 4} → W • B ≈ D → W ≈ D • B
  fromR {W} {D} e = trans (sym right-unit) (trans (back _ (sym B²)) (trans (sym assoc) (front _ e)))

  -- One more white wire.
  module Step {y : Circuit 4} (y² : y • y ≈ ε) {D : Circuit 4}
              (yb : y • B • y ≈ D • B) (yb′ : y • B • y ≈ B • D) where
    module CY = Conj {4} y y²

    stepQ : ∀ {C Q : Circuit 4} → C ≈ Q • B → y • C • y ≈ ((y • Q • y) • D) • B
    stepQ {C} {Q} e = trans (CY.⟪⟫-cong e) (trans (CY.⟪⟫-• Q B) (trans (back _ yb) (sym assoc)))

    stepR : ∀ {C R : Circuit 4} → C ≈ B • R → y • C • y ≈ B • (D • (y • R • y))
    stepR {C} {R} e = trans (CY.⟪⟫-cong e) (trans (CY.⟪⟫-• B R) (trans (front _ yb′) assoc))

  X₁² : X ↑ • X ↑ ≈ ε
  X₁² = lemma-cong↑ (X • X) ε X²

  X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
  X₂² = lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²)

  module S₁ = Step X₁² (fromR m₁′) (fromL m₁)
  module S₂ = Step X₂² (fromR m₂′) (fromL m₂)

  -- The box passes C once C is Q • B and B • R with Q ≈ R.
  fin : ∀ {C Q R : Circuit 4} → C ≈ Q • B → C ≈ B • R → Q ≈ R → B • C ≈ C • B
  fin {C} {Q} {R} cq cr qr = begin
    B • C              ≈⟨ back _ cr ⟩
    B • (B • R)        ≈⟨ trans (sym assoc) (trans (front _ B²) left-unit) ⟩
    R                  ≈⟨ sym qr ⟩
    Q                  ≈⟨ sym (trans assoc (trans (back _ B²) right-unit)) ⟩
    (Q • B) • B        ≈⟨ front _ (sym cq) ⟩
    C • B ∎

  -- A single white wire.
  one : ∀ {W D : Circuit 4} → B • W ≈ D → W • B ≈ D → B • W ≈ W • B
  one e e′ = trans e (sym e′)

  -- Through a colouring equation.
  via : ∀ {C C′ : Circuit 4} → C ≈ C′ → B • C′ ≈ C′ • B → B • C ≈ C • B
  via e h = trans (back _ e) (trans h (front _ (sym e)))

  -- The coloured box as a nested conjugation.
  f2 : N₂.⟪ col (true ∷ true ∷ true ∷ true ∷ []) B ⟫ ≈ N₂.⟪ B ⟫
  f2 = N₂.⟪⟫-cong (col⊤ B)

  f3 : col (true ∷ true ∷ true ∷ false ∷ []) B ≈ N₃.⟪ B ⟫
  f3 = trans (col₃ B) (N₃.⟪⟫-cong (col⊤ B))

private
  c335t : ∀ b c d → B • col (true ∷ b ∷ c ∷ d ∷ []) B ≈ col (true ∷ b ∷ c ∷ d ∷ []) B • B
  c335t true  true  true  = via (col⊤ B) refl
  c335t false true  true  = via (trans (col₁ (true ∷ true ∷ []) B) (N₁.⟪⟫-cong (col⊤ B))) (one m₁ m₁′)
  c335t true  false true  = via (trans (col₂ true B) f2) (one m₂ m₂′)
  c335t true  true  false = via f3 (one m₃ m₃′)
  c335t false false true  =
    via (trans (col₁ (false ∷ true ∷ []) B) (N₁.⟪⟫-cong (trans (col₂ true B) f2)))
        (fin (S₁.stepQ (fromR m₂′)) (S₁.stepR (fromL m₂))
             (U₃-sem ((X • (Ex • CZ ↑ • Ex) • X) • CZ ↑) (CZ ↑ • (X • (Ex • CZ ↑ • Ex) • X)) Eq.refl))
  c335t false true  false =
    via (trans (col₁ (true ∷ false ∷ []) B) (N₁.⟪⟫-cong f3))
        (fin (S₁.stepQ (fromR m₃′)) (S₁.stepR (fromL m₃))
             (U₃-sem ((X • CZ • X) • CZ ↑) (CZ ↑ • (X • CZ • X)) Eq.refl))
  c335t true  false false =
    via (trans (col₂ false B) (N₂.⟪⟫-cong f3))
        (fin (S₂.stepQ (fromR m₃′)) (S₂.stepR (fromL m₃))
             (U₃-sem ((X ↑ • CZ • X ↑) • (Ex • CZ ↑ • Ex)) ((Ex • CZ ↑ • Ex) • (X ↑ • CZ • X ↑)) Eq.refl))
  c335t false false false =
    via (trans (col₁ (false ∷ false ∷ []) B) (N₁.⟪⟫-cong (trans (col₂ false B) (N₂.⟪⟫-cong f3))))
        (fin (S₁.stepQ (S₂.stepQ (fromR m₃′))) (S₁.stepR (S₂.stepR (fromL m₃)))
             (U₃-sem ((X • ((X ↑ • CZ • X ↑) • (Ex • CZ ↑ • Ex)) • X) • CZ ↑)
                     (CZ ↑ • (X • ((Ex • CZ ↑ • Ex) • (X ↑ • CZ • X ↑)) • X)) Eq.refl))

c335₁ : C335 1
c335₁ (true  ∷ b ∷ c ∷ d ∷ []) = c335t b c d
c335₁ (false ∷ b ∷ c ∷ d ∷ []) = trans (back _ e) (trans (c335t b c d) (front _ (sym e)))
  where
  e : col (false ∷ b ∷ c ∷ d ∷ []) B ≈ col (true ∷ b ∷ c ∷ d ∷ []) B
  e = col-flip 0F (true ∷ b ∷ c ∷ d ∷ []) xb

------------------------------------------------------------------------
-- (336)

private
  B′ : Circuit 4
  B′ = B₁ 1

  -- White on wire 2 (179), on wire 3 ((179) under the swap of the wires
  -- 2 3), and on both (180), with the box on wire 1 black on wire 0.
  w₂ : B • N₂.⟪ B′ ⟫ ≈ N₂.⟪ B′ ⟫ • B
  w₂ = N₂.⟪⟫-≈ (sym eq179) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ B) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ B))

  e179₃ : box₃′ • N₃.⟪ box₃ ⟫ ≈ N₃.⟪ box₃ ⟫ • box₃′
  e179₃ = S₂₃.⟪⟫-≈ eq179 (S₂₃.⟪⟫-•₂ S₂₃-box₃′ S₂₃-°box₃) (S₂₃.⟪⟫-•₂ S₂₃-°box₃ S₂₃-box₃′)

  w₃ : B • N₃.⟪ B′ ⟫ ≈ N₃.⟪ B′ ⟫ • B
  w₃ = N₃.⟪⟫-≈ (sym e179₃) (N₃.⟪⟫-•₂ (N₃.⟪⟫-⟪⟫ B) refl) (N₃.⟪⟫-•₂ refl (N₃.⟪⟫-⟪⟫ B))

  w₂₃ : B • N₂.⟪ N₃.⟪ B′ ⟫ ⟫ ≈ N₂.⟪ N₃.⟪ B′ ⟫ ⟫ • B
  w₂₃ = N₂.⟪⟫-≈ (N₃.⟪⟫-≈ (sym eq180) (N₃.⟪⟫-•₂ (N₃.⟪⟫-⟪⟫ °box₃) refl) (N₃.⟪⟫-•₂ refl (N₃.⟪⟫-⟪⟫ °box₃)))
                (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ B) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ B))

  c336t : ∀ c d → B • col (true ∷ true ∷ c ∷ d ∷ []) B′ ≈ col (true ∷ true ∷ c ∷ d ∷ []) B′ • B
  c336t true  true  = via (col⊤ B′) (Canon.comm336 canon4)
  c336t false true  = via (trans (col₂ true B′) (N₂.⟪⟫-cong (col⊤ B′))) w₂
  c336t true  false = via (trans (col₃ B′) (N₃.⟪⟫-cong (col⊤ B′))) w₃
  c336t false false = via (trans (col₂ false B′) (N₂.⟪⟫-cong (trans (col₃ B′) (N₃.⟪⟫-cong (col⊤ B′))))) w₂₃

  c336b : ∀ b c d → B • col (true ∷ b ∷ c ∷ d ∷ []) B′ ≈ col (true ∷ b ∷ c ∷ d ∷ []) B′ • B
  c336b true  c d = c336t c d
  c336b false c d = trans (back _ e) (trans (c336t c d) (front _ (sym e)))
    where
    e : col (true ∷ false ∷ c ∷ d ∷ []) B′ ≈ col (true ∷ true ∷ c ∷ d ∷ []) B′
    e = col-flip (sF 0F) (true ∷ true ∷ c ∷ d ∷ []) (X₁-B xb)

c336₁ : C336 1
c336₁ (true  ∷ b ∷ c ∷ d ∷ []) = c336b b c d
c336₁ (false ∷ b ∷ c ∷ d ∷ []) =
  trans (back _ (col₀ t B′)) (trans (pass₃ (sym xb) (c336b b c d) (sym xb)) (front _ (sym (col₀ t B′))))
  where
  t : Bits 3
  t = b ∷ c ∷ d ∷ []

------------------------------------------------------------------------
-- (355)

private
  c °c : Circuit 4
  c  = CZ₃₀
  °c = P₀₃ °CZ

  N₃-c : N₃.⟪ c ⟫ ≈ °c
  N₃-c = trans (N₃.⟪⟫-cong CZ₃₀-P)
               (sym (trans (S₀₁.⟪⟫-cong (S₁₂-N₃ (P₂₃ CZ))) (S₀₁-N₃ (P₁₃ CZ))))

  N₃-°c : N₃.⟪ °c ⟫ ≈ c
  N₃-°c = N₃.⟪⟫-≈ˡ (sym N₃-c) (N₃.⟪⟫-⟪⟫ c)

  °c-ZX₃ : °c • ZX₃ ≈ ZX₃ • °c
  °c-ZX₃ = comm-inv eq208 eq208′ eq231

  c-°ZX₃ : c • N₃.⟪ ZX₃ ⟫ ≈ N₃.⟪ ZX₃ ⟫ • c
  c-°ZX₃ = N₃.⟪⟫-≈ °c-ZX₃ (N₃.⟪⟫-•₂ N₃-°c refl) (N₃.⟪⟫-•₂ refl N₃-°c)

  °ZX°XZ : N₃.⟪ ZX₃ ⟫ • N₃.⟪ XZ₃ ⟫ ≈ ε
  °ZX°XZ = trans (sym (N₃.⟪⟫-• ZX₃ XZ₃)) (trans (N₃.⟪⟫-cong eq208′) N₃.⟪⟫-ε)

  c-XZ₃ : c • XZ₃ ≈ ZX₃ • c
  c-XZ₃ = begin
    c • XZ₃                         ≈⟨ back _ eq213 ⟩
    c • (c • ΛH₂′ • c • ΛH₂′)       ≈⟨ sym assoc ⟩
    (c • c) • ΛH₂′ • c • ΛH₂′       ≈⟨ trans (front _ CZ₃₀²) left-unit ⟩
    ΛH₂′ • c • ΛH₂′                 ≈⟨ sym (back _ (back _ (trans (back _ CZ₃₀²) right-unit))) ⟩
    ΛH₂′ • c • ΛH₂′ • c • c         ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
    (ΛH₂′ • c • ΛH₂′ • c) • c       ≈⟨ front _ (sym eq212) ⟩
    ZX₃ • c ∎

core′₁ : Λ□ 3 ≈ ΛZX 3 • ΛZX 3
core′₁ = begin
  CCZX • c • CCXZ • c
    ≈⟨ cong (sym eq223′) (back _ (front _ (sym eq224))) ⟩
  (ZX₃ • N₃.⟪ ZX₃ ⟫) • c • (N₃.⟪ XZ₃ ⟫ • XZ₃) • c
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
  ZX₃ • (N₃.⟪ ZX₃ ⟫ • c) • N₃.⟪ XZ₃ ⟫ • XZ₃ • c
    ≈⟨ back _ (front _ (sym c-°ZX₃)) ⟩
  ZX₃ • (c • N₃.⟪ ZX₃ ⟫) • N₃.⟪ XZ₃ ⟫ • XZ₃ • c
    ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  ZX₃ • c • (N₃.⟪ ZX₃ ⟫ • N₃.⟪ XZ₃ ⟫) • XZ₃ • c
    ≈⟨ back _ (back _ (trans (front _ °ZX°XZ) left-unit)) ⟩
  ZX₃ • c • XZ₃ • c
    ≈⟨ back _ (trans (sym assoc) (front _ c-XZ₃)) ⟩
  ZX₃ • (ZX₃ • c) • c
    ≈⟨ back _ (trans assoc (trans (back _ CZ₃₀²) right-unit)) ⟩
  ZX₃ • ZX₃ ∎

core₁ : Λ□ 3 ≈ ΛXZ 3 • ΛXZ 3
core₁ = sym (inv-unique inv eq166 (sym core′₁))
  where
  inv : (ZX₃ • ZX₃) • (XZ₃ • XZ₃) ≈ ε
  inv = trans (by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl)
              (trans (back _ (trans (front _ eq208′) left-unit)) eq208′)
