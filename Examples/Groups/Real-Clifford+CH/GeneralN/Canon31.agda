------------------------------------------------------------------------
-- Presentations of groups
--
-- The canonical pair step of rule (31) of Figure 8 (Clément, Lemma 8.8)
--
-- At width 5 + k, with rot β the rotation on wire 0 (RotCol) and B the
-- box on wire 1 controlled by wire 0 and the wires 2 …, a rotation
-- passes the box and is inverted on the way, whatever the colour of the
-- box's control on wire 0:
--
--   rot β • col (γ ∷ δ ∷ 1…1) B ≈ col (γ ∷ δ ∷ 1…1) B • rot (not β)   (`K1`)
--
-- (δ, the colour on the box wire, does not count: X there passes B.)
-- Black on wire 0 it is Definition 2.4 — XZ = B CH B CH and ZX = CH B CH B,
-- so XZ • B = B • ZX by association and ZX • B = B • XZ by B² = ε.
-- White, the box is B • M with M the box on wire 1 with wire 0 idle
-- ((309) and (274)), which passes both rotations — CH by (280), B by
-- (335) — so it rides along.  This is the step that carries a rotation
-- across the box of a neighbouring Gray-code pair in rule (31).  Checked
-- numerically at five to seven wires first (scratchpad r5x/r31canon.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon31
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using (_∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (eq280)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; col-flip)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

  open Tools (N VRel,_===_)

  private
    Λ B M : Circuit N
    Λ = Λ□ (₄₊ k)
    B = Ex ↓ • Λ • Ex ↓
    M = Λ□ (₃₊ k) ↑

    ones : Bits (₃₊ k)
    ones = replicate (₃₊ k) true

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    passL : ∀ {a b y : Circuit N} → a • y ≈ y • a → b • y ≈ y • b → (a • b) • y ≈ y • (a • b)
    passL ea eb = trans assoc (trans (back _ eb) (trans (sym assoc) (trans (front _ ea) assoc)))

    module C₀₁ = Carry {N} Ex Ex²

    Λ² : Λ • Λ ≈ ε
    Λ² = Canon.invol canon

    B² : B • B ≈ ε
    B² = S₀₁.⟪⟫-invol Λ²

    S01X : S₀₁.⟪ X ⟫ ≈ X ↑
    S01X = X-step 0 (s≤s z≤n)

    S01X↑ : S₀₁.⟪ X ↑ ⟫ ≈ X
    S01X↑ = conj-sym Ex² S01X

    -- X on the box wire passes B.
    X↑-B : X ↑ • B ≈ B • X ↑
    X↑-B = C₀₁.carry S01X refl (Canon.x-box canon)

    -- The box white on wire 0, and its merge with B ((309), (274)).
    Bw : Circuit N
    Bw = X • B • X

    merge : B • Bw ≈ M
    merge = trans (sym (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-•₃ S01X↑ refl S01X↑)))
                  (trans (S₀₁.⟪⟫-cong (Canon.merge canon)) (Canon.wire274 canon))

    Bw-BM : Bw ≈ B • M
    Bw-BM = trans (sym (trans (sym assoc) (trans (front _ B²) left-unit))) (back _ merge)

    -- B and Bw commute: (335) under the swap.
    B-Bw : B • Bw ≈ Bw • B
    B-Bw = C₀₁.carry refl (S₀₁.⟪⟫-•₃ S01X↑ refl S01X↑) Λ-Zc
      where
      colZc : col (true ∷ false ∷ ones) Λ ≈ X ↑ • Λ • X ↑
      colZc = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) ↑ • Λ • (X • z ↑) ↑) (allT (₃₊ k))))
                    (cong right-unit (back _ right-unit))
      Λ-Zc : Λ • (X ↑ • Λ • X ↑) ≈ (X ↑ • Λ • X ↑) • Λ
      Λ-Zc = trans (back _ (sym colZc)) (trans (eq335 k below (true ∷ false ∷ ones)) (front _ colZc))

    -- M passes the rotations: CH by (280), B since M = B Bw.
    M-CH : M • CH ≈ CH • M
    M-CH = sym (trans (front _ (sym (unconj Ex²)))
                      (trans (lp ex (lp (eq280 (suc k) c) ex)) (back _ (unconj Ex²))))
      where
      ex : Ex • M ≈ M • Ex
      ex = sym (conj-comm Ex² (Canon.wire274 canon))
      lp : ∀ {x y : Circuit N} → x • M ≈ M • x → y • M ≈ M • y → (x • y) • M ≈ M • (x • y)
      lp ex ey = trans assoc (trans (back _ ey) (trans (sym assoc) (trans (front _ ex) assoc)))

    M-B : M • B ≈ B • M
    M-B = trans (front _ (sym merge)) (trans assoc (trans (back _ (sym B-Bw)) (back _ merge)))

    M-rot : ∀ β → M • rot β ≈ rot β • M
    M-rot true  = pass₂ M-CH (pass₂ M-B (pass₂ M-CH M-B))
    M-rot false = pass₂ M-B (pass₂ M-CH (pass₂ M-B M-CH))

    -- Black on wire 0: Definition 2.4.
    K1b : ∀ β → rot β • B ≈ B • rot (not β)
    K1b false = by-passoc ((□ • □ • □ • □) • □) (□ • (□ • □ • □ • □)) Eq.refl
    K1b true  = begin
      (CH • B • CH • B) • B      ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      CH • B • CH • (B • B)      ≈⟨ back _ (back _ (trans (back _ B²) right-unit)) ⟩
      CH • B • CH                ≈⟨ sym (trans (sym assoc) (trans (front _ B²) left-unit)) ⟩
      B • B • CH • B • CH ∎

    -- White on wire 0: the box is B M, and M rides along.
    K1w : ∀ β → rot β • Bw ≈ Bw • rot (not β)
    K1w β = begin
      rot β • Bw                 ≈⟨ back _ Bw-BM ⟩
      rot β • B • M              ≈⟨ trans (sym assoc) (trans (front _ (K1b β)) assoc) ⟩
      B • rot (not β) • M        ≈⟨ back _ (sym (M-rot (not β))) ⟩
      B • M • rot (not β)        ≈⟨ trans (sym assoc) (front _ (sym Bw-BM)) ⟩
      Bw • rot (not β) ∎

  ----------------------------------------------------------------------
  -- The pair step

  private
    K1t : ∀ β γ → rot β • col (γ ∷ true ∷ ones) B ≈ col (γ ∷ true ∷ ones) B • rot (not β)
    K1t β true = trans (back _ e) (trans (K1b β) (front _ (sym e)))
      where
      e : col (true ∷ true ∷ ones) B ≈ B
      e = trans (≡→≈ (Eq.cong (λ z → z • B • z) (allT N))) (trans left-unit right-unit)
    K1t β false = trans (back _ e) (trans (K1w β) (front _ (sym e)))
      where
      e : col (false ∷ true ∷ ones) B ≈ Bw
      e = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) • B • (X • z ↑)) (allT (₄₊ k))))
                (cong right-unit (back _ right-unit))

  K1 : ∀ β γ δ → rot β • col (γ ∷ δ ∷ ones) B ≈ col (γ ∷ δ ∷ ones) B • rot (not β)
  K1 β γ true  = K1t β γ
  K1 β γ false = trans (back _ e) (trans (K1t β γ) (front _ (sym e)))
    where
    e : col (γ ∷ false ∷ ones) B ≈ col (γ ∷ true ∷ ones) B
    e = col-flip (sF 0F) (γ ∷ true ∷ ones) X↑-B
