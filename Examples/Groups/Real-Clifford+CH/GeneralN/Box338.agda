------------------------------------------------------------------------
-- Presentations of groups
--
-- The box against the H gate whose box wire is a control of the box, of
-- different colourings (Clément, Lemma D.13, Equation (338), x ≠ y)
--
-- At the canonical position: the box Λ on wire 0 controlled by all the
-- other wires, black, and the H gate Hg on wire 0 with its box wire on
-- wire 1 and controls on the wires 2 … coloured y (Col).  Semantically
-- the box acts on the wires 1 … only and the H gate on wire 0 only, so
-- they commute for every y; the case y all true, the paper's x = y, is
-- GeneralN.Box338Eq, and this module does the others (`sep-all`).
--
-- The paper's induction on the width.  On four wires it is decided
-- (Base338).  At width 5 + k with y white on wire 2 (`Pair`), both
-- gates are expanded by (320) — Hg as the box on wire 1 between P ⊗ P
-- (GeneralN.Gadget322's letters, `H-word`) — and every letter of one
-- passes every letter of the other:
--
--   * two rotations: (242) or (243) between P ⊗ P (Colours' `norm-ZX`,
--     `norm-K` colour the rotation of the H gate);
--   * a rotation of the box against the smaller H gate, placed around
--     wire 3: between P ⊗ P the latter is a box, and that is (322),
--     (323) (Gadget322);
--   * the smaller box against a rotation of the H gate: conjugated by
--     the colouring, the same;
--   * the two smaller ones: the statement one width down.
--
-- A white control elsewhere is moved to wire 2 by adjacent swaps of the
-- controls, which pass both gates ((307)).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Box338
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (same-sem ; Evaluated)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111 ; eq112)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (C₂₄₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ using (D₂₄₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃ using (Aᴾ ; module Aj)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies242 complete₂ complete₃ using (eq242)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243 complete₂ complete₃ using (eq243)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; place-• ; place-cong ; place-low ; low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp ; below-suc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃
  using (col ; module Col ; col-place ; col-Ex ; norm-ZX ; norm-K ; conj-swap ; N₃-S₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; Hg ; Vb ; C338)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base338 using (d338)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (move′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget322 complete₂ complete₃
  using (L ; zx ; xz ; kb ; kb′ ; bb ; lt ; es ; word ; pass-word ; via ; module CW ;
         E320 ; lv ; Vb-word ; Gd ; gd ; S-place)

------------------------------------------------------------------------
-- The statement, white on wire 2

Sep : ℕ → Set
Sep m = ∀ (x : Bits m) →
        (₃₊ m) ⊢ Λ□ (₂₊ m) • col (true ∷ true ∷ false ∷ x) (Hg m) ≈ col (true ∷ true ∷ false ∷ x) (Hg m) • Λ□ (₂₊ m)

-- On four wires, decided.
sep₁ : Comp 4 → Sep 1
sep₁ c₄ (c ∷ []) =
  c₄ (same-sem (Λ□ 3 • col (true ∷ true ∷ false ∷ c ∷ []) (Hg 1)) (col (true ∷ true ∷ false ∷ c ∷ []) (Hg 1) • Λ□ 3)
               (Evaluated.same (d338 false c)))

------------------------------------------------------------------------
-- Word algebra

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  word-pass : ∀ {y : Circuit n} f ls → (∀ l → f l • y ≈ y • f l) → word f ls • y ≈ y • word f ls
  word-pass f ls e = sym (pass-word f ls (λ l → sym (e l)))

  -- Two products commute when their letters do, pair by pair.
  all-pairs : ∀ f g ls ls′ → (∀ l l′ → f l • g l′ ≈ g l′ • f l) → word f ls • word g ls′ ≈ word g ls′ • word f ls
  all-pairs f g ls ls′ e = word-pass f ls (λ l → pass-word g ls′ (e l))

  -- A conjugation carries a commutation.
  module Carry (c : Circuit n) (c² : c • c ≈ ε) where
    open Conj c c²
    carry : ∀ {a b a′ b′} → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → a • b ≈ b • a → a′ • b′ ≈ b′ • a′
    carry ea eb e = ⟪⟫-≈ e (⟪⟫-•₂ ea eb) (⟪⟫-•₂ eb ea)

-- P ⊗ P on the wires 0 1 passes a colouring black there.
module _ {m : ℕ} where
  open Tools ((₂₊ m) VRel,_===_)

  colP : ∀ (r : Bits m) (w : Circuit (₂₊ m)) →
         col (true ∷ true ∷ r) (PP ↓ • w • PP ↓) ≈ PP ↓ • col (true ∷ true ∷ r) w • PP ↓
  colP r w = conj-swap (sym (low-comm PP (negsB r))) w

  colP′ : ∀ (r : Bits m) (w : Circuit (₂₊ m)) →
          PP ↓ • col (true ∷ true ∷ r) w • PP ↓ ≈ col (true ∷ true ∷ r) (PP ↓ • w • PP ↓)
  colP′ r w = sym (colP r w)

------------------------------------------------------------------------
-- The step, at width 5 + k

module Step (k : ℕ) (below : Below (₁₊ (₄₊ k))) (ih : Sep (₁₊ k)) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    Λ : Circuit N
    Λ = Λ□ (₄₊ k)

    Λ₄ : Circuit (₄₊ k)
    Λ₄ = Λ□ (₃₊ k)

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv)

  private
    module C₁ = Carry {N} (Ex ↓) Ex²
    module Cp = Carry {N} (PP ↓) eq111

    -- The H gate's letters: the box on wire 1 between P ⊗ P.
    g : L → Circuit N
    g l = Aj.⟪ S₀₁.⟪ lt (suc k) l ⟫ ⟫

    E-word : Λ ≈ word (lt (suc k)) es
    E-word = E320 c₄ (suc k) below

    H-word : Hg (₂₊ k) ≈ word g es
    H-word = trans (Aj.⟪⟫-cong (Vb-word c₄ (suc k) below false)) (CW.⟪⟫-word (PP ↓) eq111 (lv (suc k) false) es)

    SS : ∀ w → S₀₁.⟪ S₀₁.⟪ w ⟫ ⟫ ≈ w
    SS w = S₀₁.⟪⟫-⟪⟫ w

    -- The gadget, one width down in its induction: at this width.
    gd′ : Gd (suc k)
    gd′ = gd c₄ (suc k) below

    -- P ⊗ P and the swap of the wires 0 1 commute.
    SP : ∀ w → S₀₁.⟪ Aj.⟪ w ⟫ ⟫ ≈ Aj.⟪ S₀₁.⟪ w ⟫ ⟫
    SP w = conj-swap (sym eq112) w

    ZX-XZ : ZX₃ • XZ₃ ≈ ε
    ZX-XZ = eq208′
    XZ-ZX : XZ₃ • ZX₃ ≈ ε
    XZ-ZX = eq208

    SA : Aj.⟪ S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ ⟫ ≈ Aᴾ true true true
    SA = Aj.⟪⟫-cong (SS ZX₃)

  --------------------------------------------------------------------
  -- Pairs, for a colouring white on wire 2

  module Pair (d : Bool) (x : Bits (₁₊ k)) where

    s : Bits N
    s = true ∷ true ∷ false ∷ d ∷ x

    t : Bits (₄₊ k)
    t = true ∷ true ∷ false ∷ x

    private
      module Cs = Col s
      module Cc = Carry (negsB s) (negs² s)

      -- The colouring passes P ⊗ P.
      colPs : ∀ w → col s (Aj.⟪ w ⟫) ≈ Aj.⟪ col s w ⟫
      colPs w = colP (false ∷ d ∷ x) w

      colS : ∀ w → S₀₁.⟪ col s w ⟫ ≈ col s (S₀₁.⟪ w ⟫)
      colS w = col-Ex s w

      -- The gadget's placed boxes.
      Pb : Bool → Circuit N
      Pb v = place 3 (col t (Vb v (suc k)))

      -- The swap of the wires 0 1 exchanges them.
      S-Pb : S₀₁.⟪ Pb false ⟫ ≈ Pb true
      S-Pb = begin
        S₀₁.⟪ place 3 (col t (B₁ (suc k))) ⟫            ≈⟨ S-place (col t (B₁ (suc k))) ⟩
        place 3 (S₀₁.⟪ col t (B₁ (suc k)) ⟫)            ≈⟨ place-cong 3 (col-Ex t (B₁ (suc k))) ⟩
        place 3 (col t (S₀₁.⟪ B₁ (suc k) ⟫))            ≈⟨ place-cong 3 (Col.⟪⟫-cong t (S₀₁.⟪⟫-⟪⟫ Λ₄)) ⟩
        place 3 (col t Λ₄) ∎

      -- The rotation between P ⊗ P passes both.
      A-Pb : ∀ v → Aᴾ true true true • Pb v ≈ Pb v • Aᴾ true true true
      A-Pb v = gd′ true x v

      -- The H gate's smaller box.
      g-bb : col s (g bb) ≈ Aj.⟪ Pb false ⟫
      g-bb = begin
        col s (Aj.⟪ S₀₁.⟪ place 3 Λ₄ ⟫ ⟫)          ≈⟨ colPs _ ⟩
        Aj.⟪ col s (S₀₁.⟪ place 3 Λ₄ ⟫) ⟫          ≈⟨ Aj.⟪⟫-cong (Cs.⟪⟫-cong (S-place Λ₄)) ⟩
        Aj.⟪ col s (place 3 (B₁ (suc k))) ⟫        ≈⟨ Aj.⟪⟫-cong (col-place true true false d x (B₁ (suc k))) ⟩
        Aj.⟪ Pb false ⟫ ∎

      -- The H gate's rotations, coloured.
      g-zx : col s (g zx) ≈ Aj.⟪ D₂₄₀ d true true ⟫
      g-zx = trans (colPs _) (Aj.⟪⟫-cong (norm-K true true d x))

      g-kb : col s (g kb) ≈ Aj.⟪ C₂₄₁ d true true ⟫
      g-kb = trans (colPs _) (Aj.⟪⟫-cong (trans (Cs.⟪⟫-cong (SS ZX₃)) (norm-ZX true true d x)))

      -- The swap of the wires 0 1 exchanges the two families.
      S-C : S₀₁.⟪ C₂₄₁ d true true ⟫ ≈ D₂₄₀ d true true
      S-C = sym (N₃-S₀₁ d _)
      S-D : S₀₁.⟪ D₂₄₀ d true true ⟫ ≈ C₂₄₁ d true true
      S-D = trans (S₀₁.⟪⟫-cong (sym S-C)) (SS _)

      -- The base pairs: ZX₃ against the two families between P ⊗ P.
      Z-D : ZX₃ • Aj.⟪ D₂₄₀ d true true ⟫ ≈ Aj.⟪ D₂₄₀ d true true ⟫ • ZX₃
      Z-D = Cp.carry (Aj.⟪⟫-⟪⟫ ZX₃) refl (eq242 true true d true true true)

      Z-C : ZX₃ • Aj.⟪ C₂₄₁ d true true ⟫ ≈ Aj.⟪ C₂₄₁ d true true ⟫ • ZX₃
      Z-C = Cp.carry (Aj.⟪⟫-⟪⟫ ZX₃) refl (eq243 true true d true true true)

      K-D : S₀₁.⟪ ZX₃ ⟫ • Aj.⟪ D₂₄₀ d true true ⟫ ≈ Aj.⟪ D₂₄₀ d true true ⟫ • S₀₁.⟪ ZX₃ ⟫
      K-D = C₁.carry refl (trans (SP _) (Aj.⟪⟫-cong S-C)) Z-C

      K-C : S₀₁.⟪ ZX₃ ⟫ • Aj.⟪ C₂₄₁ d true true ⟫ ≈ Aj.⟪ C₂₄₁ d true true ⟫ • S₀₁.⟪ ZX₃ ⟫
      K-C = C₁.carry refl (trans (SP _) (Aj.⟪⟫-cong S-D)) Z-D

      -- ZX₃ and the smaller H gate: the gadget between P ⊗ P.
      Z-bb : ZX₃ • Aj.⟪ Pb false ⟫ ≈ Aj.⟪ Pb false ⟫ • ZX₃
      Z-bb = Cp.carry (Aj.⟪⟫-⟪⟫ ZX₃) refl (A-Pb false)

      S-Pb′ : S₀₁.⟪ Pb true ⟫ ≈ Pb false
      S-Pb′ = trans (S₀₁.⟪⟫-cong (sym S-Pb)) (SS _)

      K-bb : S₀₁.⟪ ZX₃ ⟫ • Aj.⟪ Pb false ⟫ ≈ Aj.⟪ Pb false ⟫ • S₀₁.⟪ ZX₃ ⟫
      K-bb = C₁.carry refl (trans (SP _) (Aj.⟪⟫-cong S-Pb′))
               (Cp.carry (Aj.⟪⟫-⟪⟫ ZX₃) refl (A-Pb true))

      -- The smaller box and the H gate's rotations: conjugated by the
      -- colouring, the gadget.
      Pb-col : col s (Pb true) ≈ place 3 Λ₄
      Pb-col = trans (Cs.⟪⟫-cong (sym (col-place true true false d x Λ₄))) (Cs.⟪⟫-⟪⟫ (place 3 Λ₄))

      bb-g : ∀ {w} → Pb true • Aj.⟪ w ⟫ ≈ Aj.⟪ w ⟫ • Pb true → place 3 Λ₄ • col s (Aj.⟪ w ⟫) ≈ col s (Aj.⟪ w ⟫) • place 3 Λ₄
      bb-g e = Cc.carry Pb-col refl e

      bb-zx : place 3 Λ₄ • col s (g zx) ≈ col s (g zx) • place 3 Λ₄
      bb-zx = bb-g (sym (C₁.carry (SP ZX₃) S-Pb (A-Pb false)))

      bb-kb : place 3 Λ₄ • col s (g kb) ≈ col s (g kb) • place 3 Λ₄
      bb-kb = via (Cs.⟪⟫-cong SA) (bb-g (sym (A-Pb true)))

      -- The two smaller ones: the statement one width down.
      bb-bb : place 3 Λ₄ • col s (g bb) ≈ col s (g bb) • place 3 Λ₄
      bb-bb = via (trans g-bb Pp) (begin
        place 3 Λ₄ • place 3 (col t (Hg (suc k)))     ≈⟨ sym (place-• 3 Λ₄ _) ⟩
        place 3 (Λ₄ • col t (Hg (suc k)))             ≈⟨ place-cong 3 (ih x) ⟩
        place 3 (col t (Hg (suc k)) • Λ₄)             ≈⟨ place-• 3 _ Λ₄ ⟩
        place 3 (col t (Hg (suc k))) • place 3 Λ₄ ∎)
        where
        -- P ⊗ P goes inside the placement, and inside the colouring.
        Pp : Aj.⟪ Pb false ⟫ ≈ place 3 (col t (Hg (suc k)))
        Pp = begin
          PP ↓ • place 3 (col t (B₁ (suc k))) • PP ↓
            ≈⟨ sym (trans (place-• 3 (PP ↓) (col t (B₁ (suc k)) • PP ↓))
                    (cong (place-low 3 (PP {1})) (trans (place-• 3 (col t (B₁ (suc k))) (PP ↓))
                                                       (back _ (place-low 3 (PP {1})))))) ⟩
          place 3 (PP ↓ • col t (B₁ (suc k)) • PP ↓)
            ≈⟨ place-cong 3 (colP′ (false ∷ x) (B₁ (suc k))) ⟩
          place 3 (col t (Hg (suc k))) ∎

      -- Inverses.
      colinv : ∀ {w v} → w • v ≈ ε → col s (Aj.⟪ S₀₁.⟪ w ⟫ ⟫) • col s (Aj.⟪ S₀₁.⟪ v ⟫ ⟫) ≈ ε
      colinv {w} {v} e =
        trans (sym (Cs.⟪⟫-• _ _)) (trans (Cs.⟪⟫-cong (trans (sym (Aj.⟪⟫-• _ _))
          (trans (Aj.⟪⟫-cong (trans (sym (S₀₁.⟪⟫-• w v)) (trans (S₀₁.⟪⟫-cong e) S₀₁.⟪⟫-ε))) Aj.⟪⟫-ε))) Cs.⟪⟫-ε)

      K-K′ : S₀₁.⟪ ZX₃ ⟫ • S₀₁.⟪ XZ₃ ⟫ ≈ ε
      K-K′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)
      K′-K : S₀₁.⟪ XZ₃ ⟫ • S₀₁.⟪ ZX₃ ⟫ ≈ ε
      K′-K = trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε)

      -- Passing a letter of the H gate, and its inverse.
      right : ∀ {y w v} → w • v ≈ ε → v • w ≈ ε →
              y • col s (Aj.⟪ S₀₁.⟪ w ⟫ ⟫) ≈ col s (Aj.⟪ S₀₁.⟪ w ⟫ ⟫) • y →
              y • col s (Aj.⟪ S₀₁.⟪ v ⟫ ⟫) ≈ col s (Aj.⟪ S₀₁.⟪ v ⟫ ⟫) • y
      right wv vw e = comm-inv (colinv wv) (colinv vw) e

      left : ∀ {Y w v} → w • v ≈ ε → v • w ≈ ε → w • Y ≈ Y • w → v • Y ≈ Y • v
      left wv vw e = sym (comm-inv wv vw (sym e))

      -- The rotations of the box against every letter of the H gate.
      rZ : ∀ l′ → ZX₃ • col s (g l′) ≈ col s (g l′) • ZX₃
      rZ zx  = via g-zx Z-D
      rZ kb  = via g-kb Z-C
      rZ xz  = right ZX-XZ XZ-ZX (rZ zx)
      rZ kb′ = right K-K′ K′-K (rZ kb)
      rZ bb  = via g-bb Z-bb

      rK : ∀ l′ → S₀₁.⟪ ZX₃ ⟫ • col s (g l′) ≈ col s (g l′) • S₀₁.⟪ ZX₃ ⟫
      rK zx  = via g-zx K-D
      rK kb  = via g-kb K-C
      rK xz  = right ZX-XZ XZ-ZX (rK zx)
      rK kb′ = right K-K′ K′-K (rK kb)
      rK bb  = via g-bb K-bb

      rB : ∀ l′ → place 3 Λ₄ • col s (g l′) ≈ col s (g l′) • place 3 Λ₄
      rB zx  = bb-zx
      rB kb  = bb-kb
      rB xz  = right ZX-XZ XZ-ZX bb-zx
      rB kb′ = right K-K′ K′-K bb-kb
      rB bb  = bb-bb

    pair : ∀ l l′ → lt (suc k) l • col s (g l′) ≈ col s (g l′) • lt (suc k) l
    pair zx  l′ = rZ l′
    pair kb  l′ = rK l′
    pair xz  l′ = left ZX-XZ XZ-ZX (rZ l′)
    pair kb′ l′ = left K-K′ K′-K (rK l′)
    pair bb  l′ = rB l′

    main : Λ • col s (Hg (₂₊ k)) ≈ col s (Hg (₂₊ k)) • Λ
    main = begin
      Λ • col s (Hg (₂₊ k))
        ≈⟨ cong E-word (Cs.⟪⟫-cong H-word) ⟩
      word (lt (suc k)) es • col s (word g es)
        ≈⟨ back _ (CW.⟪⟫-word (negsB s) (negs² s) g es) ⟩
      word (lt (suc k)) es • word (λ l → col s (g l)) es
        ≈⟨ all-pairs (lt (suc k)) (λ l → col s (g l)) es es pair ⟩
      word (λ l → col s (g l)) es • word (lt (suc k)) es
        ≈⟨ front _ (sym (CW.⟪⟫-word (negsB s) (negs² s) g es)) ⟩
      col s (word g es) • word (lt (suc k)) es
        ≈⟨ sym (cong (Cs.⟪⟫-cong H-word) E-word) ⟩
      col s (Hg (₂₊ k)) • Λ ∎

  step : Sep (₂₊ k)
  step (d ∷ x) = Pair.main d x

------------------------------------------------------------------------
-- White on wire 2, at every width from four on

sep : ∀ k → Below (₁₊ (₄₊ k)) → Sep (₂₊ k)
sep zero    b = Step.step 0 b (sep₁ (b (n<1+n 4)))
sep (suc k) b = Step.step (suc k) b (sep k (below-suc b))
