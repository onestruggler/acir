------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled additions on three wires
--
-- The six controlled additions among wires 0, 1, 2, named by control
-- and target (the right letter acts first):
--
--     CX       1 → 0           CXʳ      0 → 1
--     CX ↑     2 → 1           CXʳ ↑    1 → 2
--     CX₂₀     2 → 0           CX₀₂     0 → 2
--
-- Conjugating by SWAP (wires 0, 1) and SWAP ↑ (wires 1, 2) permutes
-- them; the slides below record how (s- and t-slides, and σ for
-- SWAP • SWAP ↑).  Every relation among them is then a conjugate of
-- one about CX, CX ↑ and CX₂₀: the commutations of additions sharing
-- a target or a control, and the Steinberg relation, here for all
-- labels.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Wires
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Slides

module _ {m : ℕ} where

  open Width m

  -- A word g that turns a into b as it passes, past the iterates.
  slide^ : {g a b : Circuit m} (k : ℕ) → g • a ≈ b • g → g • a ^ k ≈ b ^ k • g
  slide^ zero          e = slide-ε
  slide^ (suc zero)    e = e
  slide^ (suc (suc k)) e = slide e (slide^ (suc k) e)

  slideᶠ : {g a b : Circuit m} (k : F) → g • a ≈ b • g → g • a ^ᶠ k ≈ b ^ᶠ k • g
  slideᶠ k = slide^ (toℕ k)

  -- Two slides in a row.
  slide∘ : {g h a b c : Circuit m} → g • a ≈ b • g → h • b ≈ c • h → (h • g) • a ≈ c • h • g
  slide∘ {g} {h} {a} {b} {c} ea eb = begin
    (h • g) • a       ≈⟨ assoc ⟩
    h • g • a         ≈⟨ back h ea ⟩
    h • b • g         ≈⟨ sym assoc ⟩
    (h • b) • g       ≈⟨ front g eb ⟩
    (c • h) • g       ≈⟨ assoc ⟩
    c • h • g         ∎

  -- An involution slides a word into its conjugate, and back.
  conj-slide : {g a : Circuit m} → g • g ≈ ε → g • a ≈ (g • a • g) • g
  conj-slide {g} {a} gg = sym (begin
    (g • a • g) • g    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    g • a • g • g      ≈⟨ back g (cancel-at gg a) ⟩
    g • a              ∎)

  unslide : {g a b : Circuit m} → g • g ≈ ε → g • a ≈ b • g → g • b ≈ a • g
  unslide {g} {a} {b} gg e = begin
    g • b              ≈⟨ back g (sym (I.conj← e)) ⟩
    g • g • a • g      ≈⟨ I.cancelˡ (a • g) ⟩
    a • g              ∎
    where module I = Involution gg

-- Labelled iterates one wire up.
↑ᶠ : (w : Circuit n) (k : F) → (w ^ᶠ k) ↑ ≡ (w ↑) ^ᶠ k
↑ᶠ w k = ↑-pow w (toℕ k)

------------------------------------------------------------------------
-- Two wires

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  sCX : (₂₊ n) ⊢ SWAP • CX ≈ CXʳ • SWAP
  sCX = conj-slide ss

  sCXʳ : (₂₊ n) ⊢ SWAP • CXʳ ≈ CX • SWAP
  sCXʳ = unslide ss sCX

  sM↑ : (x : F*) → (₂₊ n) ⊢ SWAP • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ • SWAP
  sM↑ x = sym (ax (swap-M (proj₁ x) (proj₂ x)))

  sM : (x : F*) → (₂₊ n) ⊢ SWAP • M⟨ x ⟩ ≈ M⟨ x ⟩ ↑ • SWAP
  sM x = unslide ss (sM↑ x)

  CXʳ-order : (₂₊ n) ⊢ CXʳ ^ p ≈ ε
  CXʳ-order = •-cancelʳ (begin
    CXʳ ^ p • SWAP     ≈⟨ sym (slide^ p sCX) ⟩
    SWAP • CX ^ p      ≈⟨ back _ CX-order ⟩
    SWAP • ε           ≈⟨ slide-ε ⟩
    ε • SWAP           ∎)
    where open Inv (₂₊ n) using (•-cancelʳ)

------------------------------------------------------------------------
-- Three wires

-- Wire 0 to wire 2.
CX₀₂ : Circuit (₃₊ n)
CX₀₂ = SWAP ↑ • CXʳ • SWAP ↑

module _ {n : ℕ} where

  open Width (₃₊ n)

  private
    tt : (₃₊ n) ⊢ SWAP ↑ • SWAP ↑ ≈ ε
    tt = SWAP↑²

    braid : (₃₊ n) ⊢ SWAP • SWAP ↑ • SWAP ≈ SWAP ↑ • SWAP • SWAP ↑
    braid = ax swap-braid

  -- SWAP ↑ exchanges wires 1 and 2.
  tCX : (₃₊ n) ⊢ SWAP ↑ • CX ≈ CX₂₀ • SWAP ↑
  tCX = conj-slide tt

  tCX₂₀ : (₃₊ n) ⊢ SWAP ↑ • CX₂₀ ≈ CX • SWAP ↑
  tCX₂₀ = unslide tt tCX

  tCXʳ : (₃₊ n) ⊢ SWAP ↑ • CXʳ ≈ CX₀₂ • SWAP ↑
  tCXʳ = conj-slide tt

  tCX₀₂ : (₃₊ n) ⊢ SWAP ↑ • CX₀₂ ≈ CXʳ • SWAP ↑
  tCX₀₂ = unslide tt tCXʳ

  tCX↑ : (₃₊ n) ⊢ SWAP ↑ • CX ↑ ≈ CXʳ ↑ • SWAP ↑
  tCX↑ = conj-slide tt

  tCXʳ↑ : (₃₊ n) ⊢ SWAP ↑ • CXʳ ↑ ≈ CX ↑ • SWAP ↑
  tCXʳ↑ = unslide tt tCX↑

  -- SWAP exchanges wires 0 and 1 (the first from rule swap-CX).
  sCX↑ : (₃₊ n) ⊢ SWAP • CX ↑ ≈ CX₂₀ • SWAP
  sCX↑ = begin
    SWAP • CX ↑                      ≈⟨ sym (cancel-in tt _) ⟩
    SWAP ↑ • SWAP ↑ • SWAP • CX ↑    ≈⟨ back _ (sym (ax swap-CX)) ⟩
    SWAP ↑ • CX • SWAP ↑ • SWAP      ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    CX₂₀ • SWAP                      ∎

  sCX₂₀ : (₃₊ n) ⊢ SWAP • CX₂₀ ≈ CX ↑ • SWAP
  sCX₂₀ = unslide (ax swap-order) sCX↑

  sCXʳ↑ : (₃₊ n) ⊢ SWAP • CXʳ ↑ ≈ CX₀₂ • SWAP
  sCXʳ↑ = begin
    SWAP • SWAP ↑ • CX ↑ • SWAP ↑
      ≈⟨ back _ (back _ (front _ (sym (I.conj← sCX₂₀)))) ⟩
    SWAP • SWAP ↑ • (SWAP • CX₂₀ • SWAP) • SWAP ↑
      ≈⟨ by-passoc (□ • □ • (□ • □ • □) • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
    (SWAP • SWAP ↑ • SWAP) • CX₂₀ • SWAP • SWAP ↑
      ≈⟨ front _ braid ⟩
    (SWAP ↑ • SWAP • SWAP ↑) • CX₂₀ • SWAP • SWAP ↑
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    SWAP ↑ • SWAP • (SWAP ↑ • CX₂₀) • SWAP • SWAP ↑
      ≈⟨ back _ (back _ (front _ tCX₂₀)) ⟩
    SWAP ↑ • SWAP • (CX • SWAP ↑) • SWAP • SWAP ↑
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □ • □)) Eq.refl ⟩
    SWAP ↑ • SWAP • CX • (SWAP ↑ • SWAP • SWAP ↑)
      ≈⟨ back _ (back _ (back _ (sym braid))) ⟩
    SWAP ↑ • SWAP • CX • (SWAP • SWAP ↑ • SWAP)
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ • □)) ((□ • (□ • □ • □) • □) • □) Eq.refl ⟩
    CX₀₂ • SWAP ∎
    where module I = Involution (ax {₃₊ n} swap-order)

  sCX₀₂ : (₃₊ n) ⊢ SWAP • CX₀₂ ≈ CXʳ ↑ • SWAP
  sCX₀₂ = unslide (ax swap-order) sCXʳ↑

  -- σ = SWAP • SWAP ↑ moves wire 0 to 1, 1 to 2 and 2 to 0.
  σCX : (₃₊ n) ⊢ (SWAP • SWAP ↑) • CX ≈ CX ↑ • SWAP • SWAP ↑
  σCX = slide∘ tCX sCX₂₀

  σCX↑ : (₃₊ n) ⊢ (SWAP • SWAP ↑) • CX ↑ ≈ CX₀₂ • SWAP • SWAP ↑
  σCX↑ = slide∘ tCX↑ sCXʳ↑

  σCX₂₀ : (₃₊ n) ⊢ (SWAP • SWAP ↑) • CX₂₀ ≈ CXʳ • SWAP • SWAP ↑
  σCX₂₀ = slide∘ tCX₂₀ sCX

  -- The multipliers.
  tM : (x : F*) → (₃₊ n) ⊢ SWAP ↑ • M⟨ x ⟩ ≈ M⟨ x ⟩ • SWAP ↑
  tM x = comm-gate₁-w↑ (M-gate (proj₁ x) (proj₂ x)) SWAP

  tM↑ : (x : F*) → (₃₊ n) ⊢ SWAP ↑ • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ ↑ • SWAP ↑
  tM↑ x = lift (sM x)

  tM↑↑ : (x : F*) → (₃₊ n) ⊢ SWAP ↑ • M⟨ x ⟩ ↑ ↑ ≈ M⟨ x ⟩ ↑ • SWAP ↑
  tM↑↑ x = lift (sM↑ x)

  -- Anything two wires up commutes with the gates on wires 0 and 1.
  sW : (w : Circuit (₁₊ n)) → (₃₊ n) ⊢ SWAP • w ↑ ↑ ≈ w ↑ ↑ • SWAP
  sW w = sym (comm-gate₂-w↑↑ SWAP-gate w)

  cW : (w : Circuit (₁₊ n)) → (₃₊ n) ⊢ CX • w ↑ ↑ ≈ w ↑ ↑ • CX
  cW w = sym (comm-gate₂-w↑↑ CX-gate w)

  -- The exchange of wires 0 and 2 commutes with SWAP ↑ when it
  -- conjugates something two wires up.
  Π-comm : (w : Circuit (₁₊ n)) →
           (₃₊ n) ⊢ SWAP ↑ • (SWAP • SWAP ↑ • w ↑ ↑ • SWAP ↑ • SWAP)
                  ≈ (SWAP • SWAP ↑ • w ↑ ↑ • SWAP ↑ • SWAP) • SWAP ↑
  Π-comm w = begin
    SWAP ↑ • SWAP • SWAP ↑ • w ↑ ↑ • SWAP ↑ • SWAP
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
    (SWAP ↑ • SWAP • SWAP ↑) • w ↑ ↑ • SWAP ↑ • SWAP
      ≈⟨ front _ (sym braid) ⟩
    (SWAP • SWAP ↑ • SWAP) • w ↑ ↑ • SWAP ↑ • SWAP
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    SWAP • SWAP ↑ • (SWAP • w ↑ ↑) • SWAP ↑ • SWAP
      ≈⟨ back _ (back _ (front _ (sW w))) ⟩
    SWAP • SWAP ↑ • (w ↑ ↑ • SWAP) • SWAP ↑ • SWAP
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □ • □)) Eq.refl ⟩
    SWAP • SWAP ↑ • w ↑ ↑ • (SWAP • SWAP ↑ • SWAP)
      ≈⟨ back _ (back _ (back _ braid)) ⟩
    SWAP • SWAP ↑ • w ↑ ↑ • (SWAP ↑ • SWAP • SWAP ↑)
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ • □)) ((□ • □ • □ • □ • □) • □) Eq.refl ⟩
    (SWAP • SWAP ↑ • w ↑ ↑ • SWAP ↑ • SWAP) • SWAP ↑ ∎

  ----------------------------------------------------------------------
  -- Commutations

  -- Same target 1, and same control 0.
  rX : (₃₊ n) ⊢ CXʳ • CX ↑ ≈ CX ↑ • CXʳ
  rX = across (slide sCX sCX₂₀) (slide sCX₂₀ sCX) XX-comm

  r02 : (₃₊ n) ⊢ CX₀₂ • CXʳ ≈ CXʳ • CX₀₂
  r02 = across (slide σCX↑ σCX₂₀) (slide σCX₂₀ σCX↑) XX2-comm

  ----------------------------------------------------------------------
  -- The Steinberg relation for all labels

  private
    module OC = Pow.Order (₃₊ n) {CX₂₀} CX₂₀-order
    module OR = Pow.Order (₃₊ n) {CXʳ} CXʳ-order

  steinberg⁰ : (x y : F) →
    (₃₊ n) ⊢ (CX ^ᶠ y) ↑ • CX ^ᶠ x • CX₂₀ ^ᶠ (x * y) ≈ CX ^ᶠ x • (CX ^ᶠ y) ↑
  steinberg⁰ x y with x ≟ 0F | y ≟ 0F
  ... | yes refl | _ = begin
    (CX ^ᶠ y) ↑ • ε • CX₂₀ ^ᶠ (0F * y)   ≈⟨ back _ (trans left-unit (OC.^ᶠ-≡ (FR.zeroˡ y))) ⟩
    (CX ^ᶠ y) ↑ • ε                      ≈⟨ slide-ε ⟩
    ε • (CX ^ᶠ y) ↑                      ∎
  ... | no _ | yes refl = begin
    ε • CX ^ᶠ x • CX₂₀ ^ᶠ (x * 0F)       ≈⟨ left-unit ⟩
    CX ^ᶠ x • CX₂₀ ^ᶠ (x * 0F)           ≈⟨ back _ (OC.^ᶠ-≡ (FR.zeroʳ x)) ⟩
    CX ^ᶠ x • ε                          ∎
  ... | no nx | no ny = steinberg (x , nx) (y , ny)

  -- CX ↑ conjugates CX by CX₂₀.
  st-cx : (c : F) → (₃₊ n) ⊢ CX ^ᶠ c • CX ↑ ≈ CX ↑ • CX ^ᶠ c • CX₂₀ ^ᶠ c
  st-cx c = sym (trans (back _ (back _ (OC.^ᶠ-≡ (Eq.sym (FR.*-identityʳ c))))) (steinberg⁰ c 1F))

  -- CX ^ᶠ e one wire up past CX ^ᶠ c.
  st-up : (c e : F) →
    (₃₊ n) ⊢ (CX ^ᶠ e) ↑ • CX ^ᶠ c ≈ CX ^ᶠ c • CX₂₀ ^ᶠ (- (c * e)) • (CX ^ᶠ e) ↑
  st-up c e = begin
    (CX ^ᶠ e) ↑ • CX ^ᶠ c
      ≈⟨ back _ (sym (trans assoc (trans (back _ (OC.^ᶠ-inverseʳ (c * e))) right-unit))) ⟩
    (CX ^ᶠ e) ↑ • (CX ^ᶠ c • CX₂₀ ^ᶠ (c * e)) • CX₂₀ ^ᶠ (- (c * e))
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □ • □) • □) Eq.refl ⟩
    ((CX ^ᶠ e) ↑ • CX ^ᶠ c • CX₂₀ ^ᶠ (c * e)) • CX₂₀ ^ᶠ (- (c * e))
      ≈⟨ front _ (steinberg⁰ c e) ⟩
    (CX ^ᶠ c • (CX ^ᶠ e) ↑) • CX₂₀ ^ᶠ (- (c * e))
      ≈⟨ trans assoc (back _ up20) ⟩
    CX ^ᶠ c • CX₂₀ ^ᶠ (- (c * e)) • (CX ^ᶠ e) ↑ ∎
    where
    up20 : (₃₊ n) ⊢ (CX ^ᶠ e) ↑ • CX₂₀ ^ᶠ (- (c * e)) ≈ CX₂₀ ^ᶠ (- (c * e)) • (CX ^ᶠ e) ↑
    up20 = trans (front _ (refl' (↑ᶠ CX e)))
             (trans (Pow.pow-comm₂ (₃₊ n) (toℕ e) (toℕ (- (c * e))) XX2-comm)
                    (back _ (refl' (Eq.sym (↑ᶠ CX e)))))

  -- The σ-conjugate: CX ↑ conjugates CX₀₂ by CXʳ.
  st-02 : (d : F) → (₃₊ n) ⊢ CX₀₂ ^ᶠ d • CX ↑ ≈ CX ↑ • CX₀₂ ^ᶠ d • CXʳ ^ᶠ (- d)
  st-02 d = begin
    CX₀₂ ^ᶠ d • CX ↑
      ≈⟨ sym (trans assoc (trans (back _ (trans assoc (back _ (OR.^ᶠ-inverseʳ d)))) (back _ right-unit))) ⟩
    (CX₀₂ ^ᶠ d • CX ↑ • CXʳ ^ᶠ d) • CXʳ ^ᶠ (- d)
      ≈⟨ front _ conj ⟩
    (CX ↑ • CX₀₂ ^ᶠ d) • CXʳ ^ᶠ (- d)
      ≈⟨ assoc ⟩
    CX ↑ • CX₀₂ ^ᶠ d • CXʳ ^ᶠ (- d) ∎
    where
    σ↑ᶠ : (₃₊ n) ⊢ (SWAP • SWAP ↑) • (CX ^ᶠ d) ↑ ≈ CX₀₂ ^ᶠ d • SWAP • SWAP ↑
    σ↑ᶠ = trans (back _ (refl' (↑ᶠ CX d))) (slideᶠ d σCX↑)
    σ20 : (₃₊ n) ⊢ (SWAP • SWAP ↑) • CX₂₀ ^ᶠ (1F * d) ≈ CXʳ ^ᶠ d • SWAP • SWAP ↑
    σ20 = trans (back _ (OC.^ᶠ-≡ (FR.*-identityˡ d))) (slideᶠ d σCX₂₀)
    conj : (₃₊ n) ⊢ CX₀₂ ^ᶠ d • CX ↑ • CXʳ ^ᶠ d ≈ CX ↑ • CX₀₂ ^ᶠ d
    conj = across (slide σ↑ᶠ (slide σCX σ20)) (slide σCX σ↑ᶠ) (steinberg⁰ 1F d)
