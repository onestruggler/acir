------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical forms of rule (32) of Figure 8 (Clément, Lemma 8.8)
--
-- At width 5 + k, with R true = ΛZX and R false = ΛXZ the rotations on
-- wire 0 controlled by the wires 1 …, two rotations commute
--
--   * on the same target, when their colourings differ on a control:
--     R α • col e (R β) ≈ col e (R β) • R α with e black on wire 0 and
--     white on wire 3, the witness (`C351w`, the paper's (351), x ≠ y);
--   * on crossed targets, each controlled by the other's target, when
--     their colourings differ off both targets: the first on wire 0
--     coloured c on wire 1, the second on wire 1 (under the swap of the
--     wires 0 1) white on wire 3 (`C352w`, the paper's (352), x ≠ y).
--
-- The paper's proof goes through (342), an H gate against an H gate on
-- a common control.  Here each rotation is a word in the H gate HG
-- (Col.Hg: H on wire 0, box wire 1) and the box K on wire 2 — (333) and
-- (334), Canon40 — and the letters commute pairwise: two boxes by
-- (335) (`F4`, and `col-pair`); an H gate and a box by (339) in
-- Canon40's form, the colourings normalised by X on the H gate's box
-- wire (X-Hg) and on the box's box wire (`KH`); two H gates, on the same
-- wires by (335) between P ⊗ P (`F1`), on crossed wires by (336)
-- between P ⊗ P (`G1`).  The point is where the H gates' box wires sit:
-- on the other gate's target, not on a common control.  Every step was
-- checked numerically at five to seven wires first (scratchpad
-- r5x/r32canon.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon32
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH ; Xat)
import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; φ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (combine ; _⇔_ ; col-col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (col-rel ; combine-lookup)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁ ; module S₁₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs² ; negs-flip ; negs-flip′ ; swB ; swapAt-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swap-braid ; swap-far)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; col-Ex ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxAnywhere complete₂ complete₃ using (col-pair)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT ; S-ZX ; S-XZ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon40 complete₂ complete₃
  using (eq333 ; eq334 ; Kcol ; eq339c ; swB-invol)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ ; col-flip)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)
  open XY k below using (X-Hg ; S-ΛH)

  -- The two rotations on wire 0 (RotCol's, at this width).
  R : Bool → Circuit N
  R = rot

  private
    Λ B K HG A : Circuit N
    Λ  = Λ□ (₄₊ k)
    B  = Ex ↓ • Λ • Ex ↓
    K  = S₁₂.⟪ B ⟫
    HG = Hg (₂₊ k)
    A  = ΛH (₃₊ k)

    Ka : Bool → Circuit N
    Ka = Kcol k below

    -- The letters of the rotations, and the rotations as words in them.
    pick : Bool → Circuit N
    pick true  = HG
    pick false = K

    w4 : Circuit N → Circuit N → Circuit N
    w4 x y = x • y • x • y

    Rw : ∀ α → R α ≈ w4 (pick α) (pick (not α))
    Rw true  = sym (eq333 k below)
    Rw false = sym (eq334 k below)

    --------------------------------------------------------------------
    -- Word algebra

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    both : ∀ {p p′ q q′ : Circuit N} → p ≈ p′ → q ≈ q′ → p • q ≈ q • p → p′ • q′ ≈ q′ • p′
    both ep eq e = trans (sym (cong ep eq)) (trans e (cong eq ep))

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    passL : ∀ {a b y : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
    passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

    fixc : ∀ {s u : Circuit N} → s • u ≈ u • s → s • s ≈ ε → s • u • s ≈ u
    fixc e s² = trans (sym assoc) (trans (front _ e) (trans assoc (trans (back _ s²) right-unit)))

    -- Words of two letters commute letter by letter.
    pass-w4 : ∀ {a b x y : Circuit N} → a • x ≈ x • a → a • y ≈ y • a → b • x ≈ x • b → b • y ≈ y • b →
              w4 a b • w4 x y ≈ w4 x y • w4 a b
    pass-w4 {a} {b} {x} {y} ax ay bx by = passL aY (passL bY (passL aY bY))
      where
      aY : a • w4 x y ≈ w4 x y • a
      aY = pass₂ ax (pass₂ ay (pass₂ ax ay))
      bY : b • w4 x y ≈ w4 x y • b
      bY = pass₂ bx (pass₂ by (pass₂ bx by))

    --------------------------------------------------------------------
    -- Colourings

    col-• : ∀ (s : Bits N) a b → col s (a • b) ≈ col s a • col s b
    col-• s a b = sym (begin
      (negsB s • a • negsB s) • (negsB s • b • negsB s)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      negsB s • a • ((negsB s • negsB s) • b • negsB s)
        ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      negsB s • a • (b • negsB s)
        ≈⟨ back _ (sym assoc) ⟩
      negsB s • (a • b) • negsB s ∎)

    col-w4 : ∀ (s : Bits N) a b → col s (w4 a b) ≈ w4 (col s a) (col s b)
    col-w4 s a b = trans (col-• s a _) (back _ (trans (col-• s b _) (back _ (trans (col-• s a b) refl))))

    col-cong : ∀ (s : Bits N) {a b : Circuit N} → a ≈ b → col s a ≈ col s b
    col-cong s e = mid _ _ e

    -- A commutation conjugated by a colouring.
    col-conj : ∀ (s : Bits N) {x y : Circuit N} → col s x • y ≈ y • col s x → x • col s y ≈ col s y • x
    col-conj s {x} {y} h = Cs.⟪⟫-≈ h (Cs.⟪⟫-•₂ (Cs.⟪⟫-⟪⟫ x) refl) (Cs.⟪⟫-•₂ refl (Cs.⟪⟫-⟪⟫ x))
      where module Cs = Conj {N} (negsB s) (negs² s)

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    X↑² : X ↑ • X ↑ ≈ ε
    X↑² = lemma-cong↑ _ _ X²

    X↑↑² : X ↑ ↑ • X ↑ ↑ ≈ ε
    X↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

    module C₀₁ = Carry {N} Ex Ex²
    module C₁₂ = Carry {N} (Ex ↑) Ex↑²
    module CX₂ = Carry {N} (X ↑ ↑) X↑↑²
    module CP  = Carry {N} (PP ↓) eq111

    -- The colouring on a wire of the swaps.
    colS₁₂ : ∀ (s : Bits N) w → S₁₂.⟪ col s w ⟫ ≈ col (swB 1 s) (S₁₂.⟪ w ⟫)
    colS₁₂ s w = S₁₂.⟪⟫-•₃ (swapAt-negsB 1 s) refl (swapAt-negsB 1 s)

    --------------------------------------------------------------------
    -- The letters under the swaps, and X on their box wires

    S₁₂-Λ : S₁₂.⟪ Λ ⟫ ≈ Λ
    S₁₂-Λ = trans (sym assoc) (trans (front _ (symAt 0)) (trans assoc (trans (back _ Ex↑²) right-unit)))

    br : Ex • Ex ↑ • Ex ≈ Ex ↑ • Ex • Ex ↑
    br = swap-braid 0 (s≤s (s≤s (s≤s z≤n)))

    -- The swap of the wires 0 1 fixes K ((307)).
    ExK : Ex • K • Ex ≈ K
    ExK = begin
      Ex • (Ex ↑ • (Ex • Λ • Ex) • Ex ↑) • Ex
        ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
      (Ex • Ex ↑ • Ex) • Λ • (Ex • Ex ↑ • Ex)
        ≈⟨ cong br (back _ br) ⟩
      (Ex ↑ • Ex • Ex ↑) • Λ • (Ex ↑ • Ex • Ex ↑)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
      Ex ↑ • (Ex • S₁₂.⟪ Λ ⟫ • Ex) • Ex ↑
        ≈⟨ mid _ _ (mid _ _ S₁₂-Λ) ⟩
      K ∎

    -- HG under the swap of the wires 0 1 is A = P ⊗ P around Λ.
    ExHG : Ex • HG • Ex ≈ A
    ExHG = trans (S₀₁.⟪⟫-cong (sym S-ΛH)) (S₀₁.⟪⟫-⟪⟫ A)

    -- X on the box wires: wire 1 of HG, wire 0 of A, wire 2 of K.
    X-A : X • A ≈ A • X
    X-A = C₀₁.carry (conj-sym Ex² (X-step 0 (s≤s z≤n))) ExHG X-Hg

    X₂-K : X ↑ ↑ • K ≈ K • X ↑ ↑
    X₂-K = sym (conj-comm X↑↑² fixK)
      where
      S₁₂X₁ : S₁₂.⟪ X ↑ ⟫ ≈ X ↑ ↑
      S₁₂X₁ = X-step 1 (s≤s (s≤s z≤n))
      S₀₁X : S₀₁.⟪ X ⟫ ≈ X ↑
      S₀₁X = X-step 0 (s≤s z≤n)
      XΛX : X • Λ • X ≈ Λ
      XΛX = fixc (Canon.x-box canon) X²
      fixK : X ↑ ↑ • K • X ↑ ↑ ≈ K
      fixK = trans (sym (S₁₂.⟪⟫-•₃ S₁₂X₁ refl S₁₂X₁))
                   (S₁₂.⟪⟫-cong (trans (sym (S₀₁.⟪⟫-•₃ S₀₁X refl S₀₁X)) (S₀₁.⟪⟫-cong XΛX)))

    X₂-X : X ↑ ↑ • X ≈ X • X ↑ ↑
    X₂-X = sym (X-↑ (X ↑))

    X₂-Ka : ∀ a → X ↑ ↑ • Ka a ≈ Ka a • X ↑ ↑
    X₂-Ka true  = X₂-K
    X₂-Ka false = pass₂ X₂-X (pass₂ X₂-K X₂-X)

    -- X on a wire around a colouring changes its bit there; X on the box
    -- wire of HG passes it.
    colX : ∀ (i : Fin N) (s : Bits N) w → Xat (toℕ i) • col s w • Xat (toℕ i) ≈ col (flipAt (toℕ i) s) w
    colX i s w = sym (trans (cong (negs-flip i s) (back _ (negs-flip′ i s)))
                            (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl))

    colHG₁ : ∀ (s : Bits N) → col (flipAt 1 s) HG ≈ col s HG
    colHG₁ s = col-flip (sF 0F) s X-Hg

    --------------------------------------------------------------------
    -- (339): K, negated on wire 0 or not, against HG in a colouring black
    -- on wire 0 and white on wire 3

    -- A colouring of K with X on wire 0 is Ka false.
    colKa : ∀ a (s : Bits (₄₊ k)) → col (a ∷ s) K ≈ col (true ∷ s) (Ka a)
    colKa true  s = refl
    colKa false s = begin
      (X • Ns) • K • (X • Ns)       ≈⟨ front _ (X-↑ (negsB s)) ⟩
      (Ns • X) • K • (X • Ns)       ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      Ns • (X • K • X) • Ns ∎
      where
      Ns : Circuit N
      Ns = negsB s ↑

    KH : ∀ a b c (r : Bits (₁₊ k)) →
         Ka a • col (true ∷ b ∷ c ∷ false ∷ r) HG ≈ col (true ∷ b ∷ c ∷ false ∷ r) HG • Ka a
    KH₁ : ∀ a c (r : Bits (₁₊ k)) →
          Ka a • col (true ∷ true ∷ c ∷ false ∷ r) HG ≈ col (true ∷ true ∷ c ∷ false ∷ r) HG • Ka a
    KH₂ : ∀ a (r : Bits (₁₊ k)) →
          Ka a • col (true ∷ true ∷ true ∷ false ∷ r) HG ≈ col (true ∷ true ∷ true ∷ false ∷ r) HG • Ka a
    KH a false c r = both refl (sym (colHG₁ (true ∷ true ∷ c ∷ false ∷ r))) (KH₁ a c r)
    KH a true  c r = KH₁ a c r

    KH₁ a false r = CX₂.carry (fixc (X₂-Ka a) X↑↑²) (colX (sF (sF 0F)) (true ∷ true ∷ true ∷ false ∷ r) HG) (KH₂ a r)
    KH₁ a true  r = KH₂ a r

    KH₂ a r = eq339c k below a (false ∷ r) (λ ())

    --------------------------------------------------------------------
    -- The four pairs of letters on the same target

    F1₁ : ∀ (r : Bits (₃₊ k)) → HG • col (true ∷ true ∷ r) HG ≈ col (true ∷ true ∷ r) HG • HG
    F1₁ r = both refl (sym form) (CP.carry refl refl (C₀₁.carry refl (col-Ex s Λ) (eq335 k below s)))
      where
      s : Bits N
      s = true ∷ true ∷ r
      form : col s HG ≈ PP ↓ • col s B • PP ↓
      form = conj-swap (sym (low-comm PP (negsB r))) B

    F1 : ∀ b (r : Bits (₃₊ k)) → HG • col (true ∷ b ∷ r) HG ≈ col (true ∷ b ∷ r) HG • HG
    F1 false r = both refl (sym (colHG₁ (true ∷ true ∷ r))) (F1₁ r)
    F1 true  r = F1₁ r

    F2 : ∀ a b c (r : Bits (₁₊ k)) → HG • col (a ∷ b ∷ c ∷ false ∷ r) K ≈ col (a ∷ b ∷ c ∷ false ∷ r) K • HG
    F2 a b c r = both refl (sym (colKa a (b ∷ c ∷ false ∷ r)))
                   (col-conj (true ∷ b ∷ c ∷ false ∷ r) (sym (KH a b c r)))

    F3 : ∀ b c (r : Bits (₁₊ k)) → K • col (true ∷ b ∷ c ∷ false ∷ r) HG ≈ col (true ∷ b ∷ c ∷ false ∷ r) HG • K
    F3 = KH true

    F4 : ∀ (s : Bits N) → K • col s K ≈ col s K • K
    F4 s = Eq.subst (λ z → K • col z K ≈ col z K • K) e
             (C₁₂.carry refl (colS₁₂ (swB 0 s′) B) (C₀₁.carry refl (col-Ex s′ Λ) (eq335 k below s′)))
      where
      s′ : Bits N
      s′ = swB 0 (swB 1 s)
      e : swB 1 (swB 0 s′) ≡ s
      e = Eq.trans (Eq.cong (swB 1) (swB-invol 0 (swB 1 s))) (swB-invol 1 s)

  ----------------------------------------------------------------------
  -- (351) at the canonical position

  C351w : ∀ α β b c (r : Bits (₁₊ k)) →
          R α • col (true ∷ b ∷ c ∷ false ∷ r) (R β) ≈ col (true ∷ b ∷ c ∷ false ∷ r) (R β) • R α
  C351w α β b c r =
    both (sym (Rw α)) (sym (trans (col-cong e (Rw β)) (col-w4 e _ _)))
         (pass-w4 (fact α β) (fact α (not β)) (fact (not α) β) (fact (not α) (not β)))
    where
    e : Bits N
    e = true ∷ b ∷ c ∷ false ∷ r
    fact : ∀ x y → pick x • col e (pick y) ≈ col e (pick y) • pick x
    fact true  true  = F1 b (c ∷ false ∷ r)
    fact true  false = F2 true b c r
    fact false true  = F3 b c r
    fact false false = F4 e

  private
    ------------------------------------------------------------------
    -- The four pairs of letters on crossed targets

    ones : Bits (₃₊ k)
    ones = replicate (₃₊ k) true

    G1 : ∀ a (r : Bits (₃₊ k)) → HG • col (a ∷ true ∷ r) (Ex • HG • Ex) ≈ col (a ∷ true ∷ r) (Ex • HG • Ex) • HG
    G1 a r = both refl (sym (trans (col-cong (a ∷ true ∷ r) ExHG) (col-A a)))
                  (CP.carry refl (sym form) (col-conj s (sym (eq336ᶜ k below s))))
      where
      s : Bits N
      s = true ∷ true ∷ r
      col-A : ∀ a → col (a ∷ true ∷ r) A ≈ col s A
      col-A true  = refl
      col-A false = col-flip 0F s X-A
      form : col s A ≈ PP ↓ • col s Λ • PP ↓
      form = conj-swap (sym (low-comm PP (negsB r))) Λ

    G2 : ∀ a c (r : Bits (₁₊ k)) →
         HG • col (a ∷ true ∷ c ∷ false ∷ r) (Ex • K • Ex) ≈ col (a ∷ true ∷ c ∷ false ∷ r) (Ex • K • Ex) • HG
    G2 a c r = both refl (sym (col-cong (a ∷ true ∷ c ∷ false ∷ r) ExK)) (F2 a true c r)

    Kc : Bool → Circuit N
    Kc c = col (true ∷ c ∷ ones) K

    -- Kc under the swap of the wires 0 1 is Ka.
    Ex-Kc : ∀ c → Ex • Ka c • Ex ≈ Kc c
    Ex-Kc c = trans (mid _ _ (sym Ka-col)) (trans (col-Ex (c ∷ true ∷ ones) K) (col-cong (true ∷ c ∷ ones) ExK))
      where
      Ka-col : col (c ∷ true ∷ ones) K ≈ Ka c
      Ka-col = trans (colKa c (true ∷ ones))
                     (trans (≡→≈ (Eq.cong (λ z → z • Ka c • z) (allT N))) (trans left-unit right-unit))

    G3 : ∀ c a d (r : Bits (₁₊ k)) →
         Kc c • col (a ∷ true ∷ d ∷ false ∷ r) (Ex • HG • Ex) ≈ col (a ∷ true ∷ d ∷ false ∷ r) (Ex • HG • Ex) • Kc c
    G3 c a d r = C₀₁.carry (Ex-Kc c) (col-Ex (true ∷ a ∷ d ∷ false ∷ r) HG) (KH c a d r)

    G4 : ∀ c (s : Bits N) → Kc c • col s (Ex • K • Ex) ≈ col s (Ex • K • Ex) • Kc c
    G4 c s = both refl (sym (col-cong s ExK)) (col-pair (true ∷ c ∷ ones) s K F4)

    -- A colouring on wire 1 does not see HG.
    HGc : ∀ c → col (true ∷ c ∷ ones) HG ≈ HG
    HGc c = trans (hc c) (trans (≡→≈ (Eq.cong (λ z → z • HG • z) (allT N))) (trans left-unit right-unit))
      where
      hc : ∀ c → col (true ∷ c ∷ ones) HG ≈ col (true ∷ true ∷ ones) HG
      hc true  = refl
      hc false = colHG₁ (true ∷ true ∷ ones)

  ----------------------------------------------------------------------
  -- (352) at the canonical position

  C352w : ∀ α β c a d (r : Bits (₁₊ k)) →
          col (true ∷ c ∷ ones) (R α) • col (a ∷ true ∷ d ∷ false ∷ r) (Ex • R β • Ex)
            ≈ col (a ∷ true ∷ d ∷ false ∷ r) (Ex • R β • Ex) • col (true ∷ c ∷ ones) (R α)
  C352w α β c a d r =
    both (sym (trans (col-cong c′ (Rw α)) (col-w4 c′ _ _)))
         (sym (trans (col-cong e (trans (E₀.⟪⟫-cong (Rw β)) (E₀.⟪⟫-•₄ refl refl refl refl))) (col-w4 e _ _)))
         (pass-w4 (fact α β) (fact α (not β)) (fact (not α) β) (fact (not α) (not β)))
    where
    module E₀ = Conj {N} Ex Ex²
    c′ e : Bits N
    c′ = true ∷ c ∷ ones
    e  = a ∷ true ∷ d ∷ false ∷ r
    fact : ∀ x y → col c′ (pick x) • col e (Ex • pick y • Ex) ≈ col e (Ex • pick y • Ex) • col c′ (pick x)
    fact true  true  = both (sym (HGc c)) refl (G1 a (d ∷ false ∷ r))
    fact true  false = both (sym (HGc c)) refl (G2 a d r)
    fact false true  = G3 c a d r
    fact false false = G4 c e

  ----------------------------------------------------------------------
  -- The rotations are rigid on wire 0: a network of the controls passes
  -- them — the swap of the wires 1 2 by (353), the higher ones by
  -- disjointness from CH and (307) for the box

  private
    R-gen : ∀ β (g : S.Gen (₄₊ k)) → φ g ↑ • R β ≈ R β • φ g ↑
    R-gen β     (S.gate₀ ())
    R-gen β     (S.gate₁ ())
    R-gen true  (S.gate₂ S.σ-gate) = S₁₂.⟪⟫-comm (S-ZX k below)
    R-gen false (S.gate₂ S.σ-gate) = S₁₂.⟪⟫-comm (S-XZ k below)
    R-gen true  (g S.↥) = pass₂ sCH (pass₂ sB (pass₂ sCH sB))
      where
      sCH : φ g ↑ ↑ • CH ≈ CH • φ g ↑ ↑
      sCH = sym (low-comm CH (φ g))
      sB : φ g ↑ ↑ • B ≈ B • φ g ↑ ↑
      sB = pass₂ (sym (low-comm Ex (φ g))) (pass₂ (Canon.swaps canon [ g S.↥ ]ʷ) (sym (low-comm Ex (φ g))))
    R-gen false (g S.↥) = pass₂ sB (pass₂ sCH (pass₂ sB sCH))
      where
      sCH : φ g ↑ ↑ • CH ≈ CH • φ g ↑ ↑
      sCH = sym (low-comm CH (φ g))
      sB : φ g ↑ ↑ • B ≈ B • φ g ↑ ↑
      sB = pass₂ (sym (low-comm Ex (φ g))) (pass₂ (Canon.swaps canon [ g S.↥ ]ʷ) (sym (low-comm Ex (φ g))))

  rot-rigid : ∀ β (v : Word (S.Gen (₄₊ k))) → net v ↑ • R β ≈ R β • net v ↑
  rot-rigid β [ g ]ʷ  = R-gen β g
  rot-rigid β ε       = trans left-unit (sym right-unit)
  rot-rigid β (u • v) = passL (rot-rigid β u) (rot-rigid β v)

  ----------------------------------------------------------------------
  -- (351) and (352) for two colourings, in the frame of the placement
  -- layer: the relative colouring decides, and the witness sits on
  -- wire 1, resp. wire 2 — moved to wire 3 by swaps of the controls

  private
    Ex↑↑² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
    Ex↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ Ex²)

    module CS₁ = Carry {N} (Ex ↑) Ex↑²
    module CS₂ = Carry {N} (Ex ↑ ↑) Ex↑↑²

    fixR₁ : ∀ β → Ex ↑ • R β • Ex ↑ ≈ R β
    fixR₁ β = fixc (R-gen β (S.gate₂ S.σ-gate)) Ex↑²

    fixR₂ : ∀ β → Ex ↑ ↑ • R β • Ex ↑ ↑ ≈ R β
    fixR₂ β = fixc (R-gen β (S.gate₂ S.σ-gate S.↥)) Ex↑↑²

    colS₁ : ∀ (s : Bits N) w → Ex ↑ • col s w • Ex ↑ ≈ col (swB 1 s) (Ex ↑ • w • Ex ↑)
    colS₁ s w = colS₁₂ s w

    colS₂ : ∀ (s : Bits N) w → Ex ↑ ↑ • col s w • Ex ↑ ↑ ≈ col (swB 2 s) (Ex ↑ ↑ • w • Ex ↑ ↑)
    colS₂ s w = S₂₃′.⟪⟫-•₃ (swapAt-negsB 2 s) refl (swapAt-negsB 2 s)
      where module S₂₃′ = Conj {N} (Ex ↑ ↑) Ex↑↑²

    combine-ones : ∀ {j} (r : Bits j) → combine r (replicate j true) ≡ r
    combine-ones []          = Eq.refl
    combine-ones (true ∷ r)  = Eq.cong (true ∷_) (combine-ones r)
    combine-ones (false ∷ r) = Eq.cong (false ∷_) (combine-ones r)

    ⇔-T : ∀ b → (true ⇔ b) ≡ b
    ⇔-T b = Eq.refl

    C351z : ∀ α β (z : Bits N) → lookupℕ 0 z ≡ true → lookupℕ 1 z ≡ false →
            R α • col z (R β) ≈ col z (R β) • R α
    C351z α β (true ∷ false ∷ z2 ∷ z3 ∷ r) Eq.refl Eq.refl =
      CS₁.carry (fixR₁ α) (trans (colS₁ e₁ (R β)) (col-cong (swB 1 e₁) (fixR₁ β)))
        (CS₂.carry (fixR₂ α) (trans (colS₂ e₂ (R β)) (col-cong (swB 2 e₂) (fixR₂ β))) (C351w α β z2 z3 r))
      where
      e₁ e₂ : Bits N
      e₂ = true ∷ z2 ∷ z3 ∷ false ∷ r
      e₁ = true ∷ z2 ∷ false ∷ z3 ∷ r
    C351z α β (false ∷ _)        () _
    C351z α β (true ∷ true ∷ _)  _  ()

    C352z : ∀ α β c (z : Bits N) → lookupℕ 1 z ≡ true → lookupℕ 2 z ≡ false →
            col (true ∷ c ∷ ones) (R α) • col z (Ex • R β • Ex) ≈ col z (Ex • R β • Ex) • col (true ∷ c ∷ ones) (R α)
    C352z α β c (a ∷ true ∷ false ∷ d ∷ r) Eq.refl Eq.refl =
      CS₂.carry (trans (colS₂ c′ (R α)) (col-cong (swB 2 c′) (fixR₂ α)))
                (trans (colS₂ e (Ex • R β • Ex)) (col-cong (swB 2 e) ExRE))
                (C352w α β c a d r)
      where
      c′ e : Bits N
      c′ = true ∷ c ∷ ones
      e  = a ∷ true ∷ d ∷ false ∷ r
      ExRE : Ex ↑ ↑ • (Ex • R β • Ex) • Ex ↑ ↑ ≈ Ex • R β • Ex
      ExRE = trans (conj-swap (sym (swap-far 0 2 (s≤s (s≤s z≤n)))) (R β)) (mid _ _ (fixR₂ β))
    C352z α β c (a ∷ false ∷ _)        () _
    C352z α β c (a ∷ true ∷ true ∷ _)  _  ()

  C351g : ∀ α β (x y : Bits N) → lookupℕ 0 x ≡ true → lookupℕ 0 y ≡ true →
          (lookupℕ 1 x ⇔ lookupℕ 1 y) ≡ false →
          col x (R α) • col y (R β) ≈ col y (R β) • col x (R α)
  C351g α β x y x0 y0 d = col-rel x y (C351z α β (combine x y) z0 z1)
    where
    z0 : lookupℕ 0 (combine x y) ≡ true
    z0 = Eq.trans (combine-lookup 0 x y (s≤s z≤n)) (Eq.cong₂ _⇔_ x0 y0)
    z1 : lookupℕ 1 (combine x y) ≡ false
    z1 = Eq.trans (combine-lookup 1 x y (s≤s (s≤s z≤n))) d

  C352g : ∀ α β (x y : Bits N) → lookupℕ 0 x ≡ true → lookupℕ 1 y ≡ true →
          (lookupℕ 2 x ⇔ lookupℕ 2 y) ≡ false →
          col x (R α) • col y (Ex • R β • Ex) ≈ col y (Ex • R β • Ex) • col x (R α)
  C352g α β (true ∷ c ∷ x′) y Eq.refl y1 d =
    both (sym ex) refl (col-rel x″ y (C352z α β c (combine x″ y) z1 z2))
    where
    x″ : Bits N
    x″ = true ∷ true ∷ x′
    ex : col (true ∷ c ∷ x′) (R α) ≈ col x″ (col (true ∷ c ∷ ones) (R α))
    ex = sym (trans (col-col x″ (true ∷ c ∷ ones) (R α))
                    (≡→≈ (Eq.cong (λ z → col (true ∷ c ∷ z) (R α)) (combine-ones x′))))
    z1 : lookupℕ 1 (combine x″ y) ≡ true
    z1 = Eq.trans (combine-lookup 1 x″ y (s≤s (s≤s z≤n))) y1
    z2 : lookupℕ 2 (combine x″ y) ≡ false
    z2 = Eq.trans (combine-lookup 2 x″ y (s≤s (s≤s (s≤s z≤n)))) d
  C352g α β (false ∷ _) y () _ _

  ----------------------------------------------------------------------
  -- Exported for (354): the letters of the rotations, and their
  -- commutations against a colouring white on wire 3

  letter : Bool → Circuit N
  letter = pick

  letters : ∀ α → R α ≈ letter α • letter (not α) • letter α • letter (not α)
  letters = Rw

  letter-comm : ∀ x y b c (r : Bits (₁₊ k)) →
                letter x • col (true ∷ b ∷ c ∷ false ∷ r) (letter y) ≈ col (true ∷ b ∷ c ∷ false ∷ r) (letter y) • letter x
  letter-comm true  true  b c r = F1 b (c ∷ false ∷ r)
  letter-comm true  false b c r = F2 true b c r
  letter-comm false true  b c r = F3 b c r
  letter-comm false false b c r = F4 (true ∷ b ∷ c ∷ false ∷ r)

  ----------------------------------------------------------------------
  -- Exported for (38): the H gate against the letters of a rotation on
  -- wire 1 (the crossed pairs G1, G2), and K, negated on wire 0 or not,
  -- against the H gate white on wire 3 (KH)

  HG-letter₁ : ∀ y a c (r : Bits (₁₊ k)) →
               letter true • col (a ∷ true ∷ c ∷ false ∷ r) (Ex • letter y • Ex) ≈
               col (a ∷ true ∷ c ∷ false ∷ r) (Ex • letter y • Ex) • letter true
  HG-letter₁ true  a c r = G1 a (c ∷ false ∷ r)
  HG-letter₁ false a c r = G2 a c r

  Kneg-HG : ∀ a b c (r : Bits (₁₊ k)) →
            Kcol k below a • col (true ∷ b ∷ c ∷ false ∷ r) (letter true) ≈
            col (true ∷ b ∷ c ∷ false ∷ r) (letter true) • Kcol k below a
  Kneg-HG = KH
