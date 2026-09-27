------------------------------------------------------------------------
-- Presentations of groups
--
-- The multi-controlled ZX is symmetric in its first two controls
-- (Clément, Lemma D.14, Equation (353), the swap at the bottom)
--
-- At width 5 + k: the swap of the wires 1 2 passes ΛZX and ΛXZ on wire 0
-- controlled by all the other wires (`eq353`, `eq353′`).  A swap higher
-- up passes the box of Definition 2.4 directly ((307)); this is the
-- paper's case (iii), and its proof:
--
--   * CH on the wires 0 1 is the H gate on wire 0 with its box wire on
--     wire 3, controlled by wire 1, and it splits on wire 2 into H● • H○,
--     the two colours there — four-wire facts, decided (Base353);
--   * H○ passes the box B of Definition 2.4, on wire 1 controlled by the
--     rest: C339's H gate, merged over every colouring of the wires 4 …
--     (MergeAll's `merge-top₃`), is a four-wire gate, which passes C339's
--     box because each factor does (339); under the permutation of the
--     bottom wires carrying C339's box to B it is H○ (`B-o`); and H●
--     passes B negated on wire 2 likewise (`Bo-h`);
--   * so ΛZX = CH B CH B = H● B H● B = H● B′ H● B′ (`ZX-form`), where B′,
--     B times B negated on wire 2, is the box with wire 2 idle (309) —
--     and the swap of the wires 1 2 fixes H● (decided) and B′ ((274):
--     it moves the box wire of B′ along its idle wire).
--
-- The form of ΛXZ with the controls on the wires 1 2 exchanged
-- (`XZ-S`) is what rule (40) of Figure 8 decodes to.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.ZX353
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (true ; false)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n ; ≤-refl)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁ ; module S₁₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (local-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-zero)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swap-braid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (box274)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq299)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMergeAt complete₂ complete₃ using (merge-at ; merge-at′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll as MergeAll
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; conj-swap ; N₂-S₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (P₁₃ ; Hg₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base353
  using (Lm ; H○ ; H● ; e-CH ; e-comm ; e-○² ; e-●² ; e-S)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box339 complete₂ complete₃ using (P₁₃² ; flip₂ ; eq339)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338 complete₂ complete₃ using (module Carry)

------------------------------------------------------------------------
-- Products over lists

module _ {n : ℕ} {A : Set} where
  open Tools (n VRel,_===_)

  -- A conjugation by an involution, factor by factor.
  ∏-conj : ∀ (c : Circuit n) → c • c ≈ ε → ∀ (xs : List A) g →
           c • ∏ xs g • c ≈ ∏ xs (λ a → c • g a • c)
  ∏-conj c c² []       g = trans (back _ left-unit) c²
  ∏-conj c c² (x ∷ xs) g = trans (Conj.⟪⟫-• c c² (g x) (∏ xs g)) (back _ (∏-conj c c² xs g))

  ∏-cong : ∀ (xs : List A) {g g′ : A → Circuit n} → (∀ a → g a ≈ g′ a) → ∏ xs g ≈ ∏ xs g′
  ∏-cong []       e = refl
  ∏-cong (x ∷ xs) e = cong (e x) (∏-cong xs e)

  -- What passes every factor passes the product.
  pass-∏ : ∀ {y : Circuit n} (xs : List A) g → (∀ a → y • g a ≈ g a • y) → y • ∏ xs g ≈ ∏ xs g • y
  pass-∏ []       g e = trans right-unit (sym left-unit)
  pass-∏ (x ∷ xs) g e =
    trans (sym assoc) (trans (front _ (e x)) (trans assoc (trans (back _ (pass-∏ xs g e)) (sym assoc))))

-- No colours.
allT : ∀ j → negsB (replicate j true) ≡ ε
allT zero    = Eq.refl
allT (suc j) = Eq.cong (λ w → w ↑) (allT j)

------------------------------------------------------------------------
-- (353)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N m′ : ℕ
    N  = ₁₊ (₄₊ k)
    m′ = ₁₊ k

    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

  open Tools (N VRel,_===_)
  open SS.Below 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ using (by-sem)
  open MergeAll (₃₊ k) (mergesₙ k completes) using (merge-top₃)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    Λ B Bo Bp h o : Circuit N
    Λ  = Λ□ (₄₊ k)
    B  = Ex ↓ • Λ • Ex ↓
    Bo = N₂.⟪ B ⟫
    Bp = S₀₁.⟪ S₁₂.⟪ Λ□ (₃₊ k) ↑ ⟫ ⟫
    h  = H● ↓ᵏ m′
    o  = H○ ↓ᵏ m′

    X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
    X₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ X²)

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    Ex↑↑² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
    Ex↑↑² = lemma-cong↑ _ _ Ex↑²′
      where
      Ex↑²′ : (₄₊ k) ⊢ Ex ↑ • Ex ↑ ≈ ε
      Ex↑²′ = lemma-cong↑ _ _ Ex²

    module C₁ = Carry {N} (Ex ↓) Ex²
    module C₂ = Carry {N} (X ↑ ↑) X₂²

    --------------------------------------------------------------------
    -- The four-wire facts, weakened

    e₁ : CH ≈ h • o
    e₁ = by-sem (CH ↓) (H● • H○) (Evaluated.same e-CH) {m′}

    e₂ : o • h ≈ h • o
    e₂ = by-sem (H○ • H●) (H● • H○) (Evaluated.same e-comm) {m′}

    e₃ : o • o ≈ ε
    e₃ = by-sem (H○ • H○) ε (Evaluated.same e-○²) {m′}

    e₃′ : h • h ≈ ε
    e₃′ = by-sem (H● • H●) ε (Evaluated.same e-●²) {m′}

    e₄ : Ex ↑ • h • Ex ↑ ≈ h
    e₄ = by-sem (Ex ↑ • H● • Ex ↑) H● (Evaluated.same e-S) {m′}

    --------------------------------------------------------------------
    -- C339's box passes its H gate merged over the wires 4 …

    F : Circuit N → Circuit N
    F w = N₂.⟪ P₁₃ • S₀₁.⟪ w ⟫ • P₁₃ ⟫

    G2 : Bits m′ → Circuit N
    G2 y = col (true ∷ true ∷ false ∷ true ∷ y) (Hg₃ m′)

    loc : ∀ (u : Circuit 4) (y : Bits m′) → (u ↓ᵏ m′) • negsB y ↑ ↑ ↑ ↑ ≈ negsB y ↑ ↑ ↑ ↑ • (u ↓ᵏ m′)
    loc u y = local-comm u (negsB y)

    G2-F : ∀ y → G2 y ≈ F (col (true ∷ true ∷ true ∷ true ∷ y) Λ)
    G2-F y = begin
      col (true ∷ true ∷ false ∷ true ∷ y) (Hg₃ m′)
        ≈⟨ trans (sym (N₂.⟪⟫-⟪⟫ _)) (N₂.⟪⟫-cong (flip₂ (true ∷ y) (Hg₃ m′))) ⟩
      N₂.⟪ col (true ∷ true ∷ true ∷ true ∷ y) (P₁₃ • B • P₁₃) ⟫
        ≈⟨ N₂.⟪⟫-cong (trans (conj-swap (sym (loc (P₁₃ {0}) y)) B)
                              (mid _ _ (conj-swap (sym (loc Ex y)) Λ))) ⟩
      F (col (true ∷ true ∷ true ∷ true ∷ y) Λ) ∎

    F-cong : ∀ {w w′} → w ≈ w′ → F w ≈ F w′
    F-cong e = N₂.⟪⟫-cong (mid _ _ (S₀₁.⟪⟫-cong e))

    F-∏ : ∀ (g : Bits m′ → Circuit N) → F (∏ (allBits m′) g) ≈ ∏ (allBits m′) (λ y → F (g y))
    F-∏ g = trans (N₂.⟪⟫-cong (trans (mid _ _ (∏-conj (Ex ↓) Ex² (allBits m′) g))
                                      (∏-conj P₁₃ P₁₃² (allBits m′) (λ y → S₀₁.⟪ g y ⟫))))
                  (∏-conj (X ↑ ↑) X₂² (allBits m′) (λ y → P₁₃ • S₀₁.⟪ g y ⟫ • P₁₃))

    merged : ∏ (allBits m′) G2 ≈ Lm ↓ᵏ m′
    merged = begin
      ∏ (allBits m′) G2
        ≈⟨ ∏-cong (allBits m′) G2-F ⟩
      ∏ (allBits m′) (λ y → F (col (true ∷ true ∷ true ∷ true ∷ y) Λ))
        ≈⟨ sym (F-∏ (λ y → col (true ∷ true ∷ true ∷ true ∷ y) Λ)) ⟩
      F (∏ (allBits m′) (λ y → col (true ∷ true ∷ true ∷ true ∷ y) Λ))
        ≈⟨ F-cong (merge-top₃ m′ ≤-refl) ⟩
      F (Λ□ 3 ↓ᵏ m′) ∎

    Λ-col : col (true ∷ true ∷ true ∷ true ∷ replicate m′ true) Λ ≈ Λ
    Λ-col = trans (≡→≈ (Eq.cong (λ z → z ↑ ↑ ↑ ↑ • Λ • z ↑ ↑ ↑ ↑) (allT m′))) (trans left-unit right-unit)

    Λ-G2 : ∀ y → Λ • G2 y ≈ G2 y • Λ
    Λ-G2 y = trans (front _ (sym Λ-col)) (trans (eq339 k below true (replicate m′ true) y) (back _ Λ-col))

    Λ-Lm : Λ • (Lm ↓ᵏ m′) ≈ (Lm ↓ᵏ m′) • Λ
    Λ-Lm = trans (back _ (sym merged)) (trans (pass-∏ (allBits m′) G2 Λ-G2) (front _ merged))

    --------------------------------------------------------------------
    -- Carried to the box of Definition 2.4

    T13 : Circuit N
    T13 = Ex ↑ • Ex ↑ ↑ • Ex ↑

    T13² : T13 • T13 ≈ ε
    T13² = begin
      (Ex ↑ • Ex ↑ ↑ • Ex ↑) • (Ex ↑ • Ex ↑ ↑ • Ex ↑)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      Ex ↑ • Ex ↑ ↑ • (Ex ↑ • Ex ↑) • Ex ↑ ↑ • Ex ↑
        ≈⟨ back _ (back _ (trans (front _ Ex↑²) left-unit)) ⟩
      Ex ↑ • Ex ↑ ↑ • Ex ↑ ↑ • Ex ↑
        ≈⟨ back _ (trans (sym assoc) (trans (front _ Ex↑↑²) left-unit)) ⟩
      Ex ↑ • Ex ↑
        ≈⟨ Ex↑² ⟩
      ε ∎

    pass₂ : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    T13-Λ : T13 • Λ ≈ Λ • T13
    T13-Λ = sym (pass₂ (sym (symAt 0)) (pass₂ (sym (symAt 1)) (sym (symAt 0))))

    T13-fix : T13 • Λ • T13 ≈ Λ
    T13-fix = trans (sym assoc) (trans (front _ T13-Λ) (trans assoc (trans (back _ T13²) right-unit)))

    module Ct = Carry {N} T13 T13²

  -- (c): H○ passes the box.
  B-o : B • o ≈ o • B
  B-o = C₁.carry refl refl (Ct.carry T13-fix refl Λ-Lm)

  -- (d): H● passes the box negated on wire 2.
  Bo-h : Bo • h ≈ h • Bo
  Bo-h = C₂.carry refl refl B-o

  private
    --------------------------------------------------------------------
    -- (309) on wire 2, and (274)

    Λ² : Λ • Λ ≈ ε
    Λ² = eq299 (₁₊ k) c

    Bo² : Bo • Bo ≈ ε
    Bo² = N₂.⟪⟫-invol (S₀₁.⟪⟫-invol Λ²)

    pl2 : placeAt 2 (Λ□ (₃₊ k)) ≈ S₁₂.⟪ Λ□ (₃₊ k) ↑ ⟫
    pl2 = begin
      placeAt 2 (Λ□ (₃₊ k))
        ≈⟨ placeAt-step 1 (Λ□ (₃₊ k)) (s≤s (s≤s z≤n)) ⟩
      Ex ↑ • placeAt 1 (Λ□ (₃₊ k)) • Ex ↑
        ≈⟨ mid _ _ (trans (placeAt-step 0 (Λ□ (₃₊ k)) (s≤s z≤n)) (mid _ _ (placeAt-zero (Λ□ (₃₊ k))))) ⟩
      Ex ↑ • (Ex • Λ□ (₃₊ k) ↑ • Ex) • Ex ↑
        ≈⟨ mid _ _ (box274 (suc k) c) ⟩
      S₁₂.⟪ Λ□ (₃₊ k) ↑ ⟫ ∎

    SN : S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫ ≈ Bo
    SN = sym (N₂-S₀₁ false Λ)

    merge-B : B • Bo ≈ Bp
    merge-B = begin
      B • Bo                             ≈⟨ back _ (sym SN) ⟩
      S₀₁.⟪ Λ ⟫ • S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫       ≈⟨ sym (S₀₁.⟪⟫-• Λ (N₂.⟪ Λ ⟫)) ⟩
      S₀₁.⟪ Λ • N₂.⟪ Λ ⟫ ⟫               ≈⟨ S₀₁.⟪⟫-cong (trans (merge-at k c symAt 1 (s≤s (s≤s z≤n))) pl2) ⟩
      Bp ∎

    merge-B′ : Bo • B ≈ Bp
    merge-B′ = begin
      Bo • B                             ≈⟨ front _ (sym SN) ⟩
      S₀₁.⟪ N₂.⟪ Λ ⟫ ⟫ • S₀₁.⟪ Λ ⟫       ≈⟨ sym (S₀₁.⟪⟫-• (N₂.⟪ Λ ⟫) Λ) ⟩
      S₀₁.⟪ N₂.⟪ Λ ⟫ • Λ ⟫               ≈⟨ S₀₁.⟪⟫-cong (trans (merge-at′ k c symAt 1 (s≤s (s≤s z≤n))) pl2) ⟩
      Bp ∎

    -- The swap of the wires 1 2 moves the box wire of Bp along its idle
    -- wire.
    S-Bp : S₁₂.⟪ Bp ⟫ ≈ Bp
    S-Bp = begin
      Ex ↑ • (Ex • (Ex ↑ • L • Ex ↑) • Ex) • Ex ↑
        ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
      (Ex ↑ • Ex • Ex ↑) • L • (Ex ↑ • Ex • Ex ↑)
        ≈⟨ cong (sym br) (back _ (sym br)) ⟩
      (Ex • Ex ↑ • Ex) • L • (Ex • Ex ↑ • Ex)
        ≈⟨ by-passoc ((□ • □ • □) • □ • (□ • □ • □)) (□ • (□ • (□ • □ • □) • □) • □) Eq.refl ⟩
      Ex • (Ex ↑ • (Ex • L • Ex) • Ex ↑) • Ex
        ≈⟨ mid _ _ (mid _ _ (box274 (suc k) c)) ⟩
      Bp ∎
      where
      L : Circuit N
      L = Λ□ (₃₊ k) ↑
      br : Ex • Ex ↑ • Ex ≈ Ex ↑ • Ex • Ex ↑
      br = swap-braid 0 (s≤s (s≤s (s≤s z≤n)))

  --------------------------------------------------------------------
  -- The forms

  ZX-form : ΛZX (₄₊ k) ≈ h • Bp • h • Bp
  ZX-form = begin
    CH • B • CH • B
      ≈⟨ cong e₁ (back _ (front _ (trans e₁ (sym e₂)))) ⟩
    (h • o) • B • (o • h) • B
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    h • (o • B) • o • h • B
      ≈⟨ back _ (front _ (sym B-o)) ⟩
    h • (B • o) • o • h • B
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    h • B • (o • o) • h • B
      ≈⟨ back _ (back _ (trans (front _ e₃) left-unit)) ⟩
    h • B • h • B
      ≈⟨ back _ (back _ (sym (trans (front _ Bo²) left-unit))) ⟩
    h • B • (Bo • Bo) • h • B
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • □) • (□ • □) • □) Eq.refl ⟩
    h • (B • Bo) • (Bo • h) • B
      ≈⟨ back _ (back _ (front _ Bo-h)) ⟩
    h • (B • Bo) • (h • Bo) • B
      ≈⟨ by-passoc (□ • (□ • □) • (□ • □) • □) (□ • (□ • □) • □ • (□ • □)) Eq.refl ⟩
    h • (B • Bo) • h • (Bo • B)
      ≈⟨ back _ (cong merge-B (back _ merge-B′)) ⟩
    h • Bp • h • Bp ∎

  XZ-form : ΛXZ (₄₊ k) ≈ Bp • h • Bp • h
  XZ-form = begin
    B • CH • B • CH
      ≈⟨ back _ (cong e₁ (back _ (trans e₁ (sym e₂)))) ⟩
    B • (h • o) • B • (o • h)
      ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    B • h • (o • B) • o • h
      ≈⟨ back _ (back _ (front _ (sym B-o))) ⟩
    B • h • (B • o) • o • h
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    B • h • B • (o • o) • h
      ≈⟨ back _ (back _ (back _ (trans (front _ e₃) left-unit))) ⟩
    B • h • B • h
      ≈⟨ back _ (sym (trans (front _ Bo²) left-unit)) ⟩
    B • (Bo • Bo) • h • B • h
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) ((□ • □) • (□ • □) • □ • □) Eq.refl ⟩
    (B • Bo) • (Bo • h) • B • h
      ≈⟨ back _ (front _ Bo-h) ⟩
    (B • Bo) • (h • Bo) • B • h
      ≈⟨ by-passoc ((□ • □) • (□ • □) • □ • □) ((□ • □) • □ • (□ • □) • □) Eq.refl ⟩
    (B • Bo) • h • (Bo • B) • h
      ≈⟨ cong merge-B (back _ (front _ merge-B′)) ⟩
    Bp • h • Bp • h ∎

  S-ZX : S₁₂.⟪ ΛZX (₄₊ k) ⟫ ≈ ΛZX (₄₊ k)
  S-ZX = trans (S₁₂.⟪⟫-cong ZX-form) (trans (S₁₂.⟪⟫-•₄ e₄ S-Bp e₄ S-Bp) (sym ZX-form))

  S-XZ : S₁₂.⟪ ΛXZ (₄₊ k) ⟫ ≈ ΛXZ (₄₊ k)
  S-XZ = trans (S₁₂.⟪⟫-cong XZ-form) (trans (S₁₂.⟪⟫-•₄ S-Bp e₄ S-Bp e₄) (sym XZ-form))

  -- (353), a = 0 and a = 1, the swap of the wires 1 2.
  eq353 : Ex ↑ • ΛZX (₄₊ k) ≈ ΛZX (₄₊ k) • Ex ↑
  eq353 = S₁₂.⟪⟫-comm S-ZX

  eq353′ : Ex ↑ • ΛXZ (₄₊ k) ≈ ΛXZ (₄₊ k) • Ex ↑
  eq353′ = S₁₂.⟪⟫-comm S-XZ

  -- ΛXZ with its first two controls exchanged: the box of Definition 2.4
  -- on wire 2 and CH from wire 2.
  XZ-S : ΛXZ (₄₊ k) ≈ S₁₂.⟪ B ⟫ • S₁₂.⟪ CH ⟫ • S₁₂.⟪ B ⟫ • S₁₂.⟪ CH ⟫
  XZ-S = trans (sym S-XZ) (S₁₂.⟪⟫-•₄ refl refl refl refl)
