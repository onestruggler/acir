------------------------------------------------------------------------
-- Presentations of groups
--
-- Translations past linear circuits
--
-- The translation by a vector b is Xc b = X^(b₀) on wire 0, X^(b₁) on
-- wire 1, … .  A linear generator y moves a translation in front of
-- it, transformed by y (X-push):
--
--     y • Xc b ≈ Xc (b ⋆ˣ y) • y
--
-- a multiplier scales the label (rule (3)), CX adds the label of its
-- control to that of its target (rule (6)) and leaves a translation of
-- its target alone, and SWAP exchanges labels.  That CX commutes with
-- X on its target is not a rule: rule (6) makes X on wire 0 the
-- commutator of CX⁻¹ and X⁻¹ on wire 1, which is the shape of the
-- Steinberg relation (Linear.Lib.Steinberg), so for odd p it follows
-- from its conjugate by M₂ and for p = 2 from the generators being
-- involutions.  Translations compose by adding vectors (Xc-add).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Affine
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc ; _≤_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; two≢0 ; toℕ-1 ; module FR
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- X on one wire

module _ {n : ℕ} where

  open Width (₁₊ n)
  private
    module OX = Pow.Order (₁₊ n) {X} X-order

  -- Rule (3): a multiplier scales a translation.
  M-X : (x : F*) → (₁₊ n) ⊢ M⟨ x ⟩ • X ≈ X ^ᶠ proj₁ x • M⟨ x ⟩
  M-X x = begin
    M⟨ x ⟩ • X                                    ≈⟨ front _ (sym (ax (ax3 x))) ⟩
    (X ^ᶠ proj₁ x • M⟨ x ⟩ • X ^ᶠ (- 1F)) • X     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    X ^ᶠ proj₁ x • M⟨ x ⟩ • X ^ᶠ (- 1F) • X       ≈⟨ back _ (back _ (OX.^ᶠ-inverseˡ 1F)) ⟩
    X ^ᶠ proj₁ x • M⟨ x ⟩ • ε                     ≈⟨ back _ right-unit ⟩
    X ^ᶠ proj₁ x • M⟨ x ⟩                         ∎

  M-Xᶠ : (x : F*) (c : F) → (₁₊ n) ⊢ M⟨ x ⟩ • X ^ᶠ c ≈ X ^ᶠ (c * proj₁ x) • M⟨ x ⟩
  M-Xᶠ x c = trans (slideᶠ c (M-X x)) (front _ (trans (OX.^ᶠ-* (proj₁ x) c) (OX.^ᶠ-≡ (FR.*-comm _ c))))

------------------------------------------------------------------------
-- X on the target of CX

module _ {n : ℕ} where

  open Width (₂₊ n)
  open Inv (₂₊ n) using (•-cancelʳ)

  private
    module OX = Pow.Order (₁₊ n) {X} X-order

    a b : Circuit (₂₊ n)
    a = CX ^ᶠ (- 1F)
    b = (X ^ᶠ (- 1F)) ↑

    aCX : (₂₊ n) ⊢ a • CX ≈ ε
    aCX = CX-invˡ 1F

    CXa : (₂₊ n) ⊢ CX • a ≈ ε
    CXa = CX-invʳ 1F

    bX↑ : (₂₊ n) ⊢ b • X ↑ ≈ ε
    bX↑ = lift (OX.^ᶠ-inverseˡ 1F)

    X↑b : (₂₊ n) ⊢ X ↑ • b ≈ ε
    X↑b = lift (OX.^ᶠ-inverseʳ 1F)

    -- Rule (6): X is a commutator.
    X≈ : (₂₊ n) ⊢ X ≈ CX • X ↑ • a • b
    X≈ = sym (begin
      CX • X ↑ • a • b                ≈⟨ trans (sym assoc) (front _ (ax ax6)) ⟩
      (X • X ↑ • CX) • a • b          ≈⟨ by-passoc ((□ • □ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
      X • X ↑ • (CX • a) • b          ≈⟨ back _ (back _ (trans (front _ CXa) left-unit)) ⟩
      X • X ↑ • b                     ≈⟨ back _ X↑b ⟩
      X • ε                           ≈⟨ right-unit ⟩
      X                               ∎)

    F1 : (₂₊ n) ⊢ b • a • X ≈ a • b
    F1 = begin
      b • a • X                       ≈⟨ back _ (back _ X≈) ⟩
      b • a • CX • X ↑ • a • b        ≈⟨ back _ (trans (sym assoc) (trans (front _ aCX) left-unit)) ⟩
      b • X ↑ • a • b                 ≈⟨ trans (sym assoc) (trans (front _ bX↑) left-unit) ⟩
      a • b                           ∎

    module S = Steinberg F1

    -- For odd p, conjugating by M₂.
    F2 : 1 ≤ p-2 → (₂₊ n) ⊢ b • (a • a) • (X • X) ≈ (a • a) • b
    F2 odd = across (slide Mb (slide Ma MX)) (slide Ma Mb) F1
      where
      two : F*
      two = 2F , two≢0 odd
      Ma : (₂₊ n) ⊢ M⟨ two ⟩ • a ≈ (a • a) • M⟨ two ⟩
      Ma = trans (M-CXᶠ two (- 1F))
             (front _ (trans (CX-≡ (solve 0 ((:- con (ℤ.+ 1)) :* (con (ℤ.+ 1) :+ con (ℤ.+ 1))
                                             := (:- con (ℤ.+ 1)) :+ (:- con (ℤ.+ 1))) Eq.refl))
                             (sym (CX-+ (- 1F) (- 1F)))))
      MX : (₂₊ n) ⊢ M⟨ two ⟩ • X ≈ (X • X) • M⟨ two ⟩
      MX = trans (M-X two) (front _ OX'.^ᶠ-2)
        where module OX' = Pow.Order (₂₊ n) {X} X-order
      Mb : (₂₊ n) ⊢ M⟨ two ⟩ • b ≈ b • M⟨ two ⟩
      Mb = sym (comm-gate₁-w↑ (M-gate 2F (two≢0 odd)) (X ^ᶠ (- 1F)))

    -- For p = 2 the three are involutions.
    sq : {m : ℕ} {w : Circuit m} → p-2 ≡ 0 → m ⊢ w ^ p ≈ ε → m ⊢ w • w ≈ ε
    sq {m} {w} e wp = W.trans (W.refl' (Eq.cong (λ k → w ^ suc (suc k)) (Eq.sym e))) wp
      where module W = Width m

    -- -1 = 1.
    neg1 : {m : ℕ} {w : Circuit m} → p-2 ≡ 0 → m ⊢ w ^ᶠ (- 1F) ≈ w
    neg1 {m} {w} e = Width.refl' m (Eq.cong (w ^_) (Eq.trans toℕ-1 (Eq.cong suc e)))

    module W1 = Width (₁₊ n)

    module S2 (e : p-2 ≡ 0) =
      S.Order2 (trans (cong (neg1 e) (neg1 e)) (sq e CX-order))
               (lift (W1.trans (W1.cong (neg1 e) (neg1 e)) (sq e X-order)))
               (sq e X-order)

    even : ¬ 1 ≤ p-2 → p-2 ≡ 0
    even ¬odd = ℕP.n<1⇒n≡0 (ℕP.≰⇒> ¬odd)

    -- From a = CX⁻¹ back to CX.
    from-a : (₂₊ n) ⊢ a • X ≈ X • a → (₂₊ n) ⊢ CX • X ≈ X • CX
    from-a e = begin
      CX • X                       ≈⟨ sym (cancel-at aCX _) ⟩
      (CX • X) • a • CX            ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
      CX • (X • a) • CX            ≈⟨ back _ (front _ (sym e)) ⟩
      CX • (a • X) • CX            ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (CX • a) • X • CX            ≈⟨ trans (front _ CXa) left-unit ⟩
      X • CX                       ∎

  CX-X : (₂₊ n) ⊢ CX • X ≈ X • CX
  CX-X with 1 ℕP.≤? p-2
  ... | yes odd = from-a (S.comm-F2 (F2 odd))
  ... | no ¬odd = from-a (S2.comm-a (even ¬odd))

------------------------------------------------------------------------
-- Iterates of X past the linear generators

module _ {n : ℕ} where

  open Width (₂₊ n)
  private
    module OX = Pow.Order (₂₊ n) {X} X-order

  CX-Xᶠ : (c : F) → (₂₊ n) ⊢ CX • X ^ᶠ c ≈ X ^ᶠ c • CX
  CX-Xᶠ c = slideᶠ c CX-X

  X∥X↑ : (₂₊ n) ⊢ X • X ↑ ≈ X ↑ • X
  X∥X↑ = sym (comm-gate₁-w↑ X-gate X)

  -- Rule (6), iterated: X on the control of CX.
  CX-X↑ᶠ : (d : F) → (₂₊ n) ⊢ CX • (X ^ᶠ d) ↑ ≈ (X ^ᶠ d • (X ^ᶠ d) ↑) • CX
  CX-X↑ᶠ d = begin
    CX • (X ^ᶠ d) ↑                     ≈⟨ back _ (refl' (↑ᶠ X d)) ⟩
    CX • (X ↑) ^ᶠ d                     ≈⟨ slideᶠ d (trans (ax ax6) (sym assoc)) ⟩
    (X • X ↑) ^ᶠ d • CX                 ≈⟨ front _ (Pow.pow-• (₂₊ n) (toℕ d) X∥X↑) ⟩
    (X ^ᶠ d • (X ↑) ^ᶠ d) • CX          ≈⟨ front _ (back _ (refl' (Eq.sym (↑ᶠ X d)))) ⟩
    (X ^ᶠ d • (X ^ᶠ d) ↑) • CX          ∎

  -- SWAP exchanges translations.
  sX : (₂₊ n) ⊢ SWAP • X ≈ X ↑ • SWAP
  sX = unslide (ax swap-order) (sym (ax swap-X))

  sXᶠ : (c : F) → (₂₊ n) ⊢ SWAP • X ^ᶠ c ≈ (X ^ᶠ c) ↑ • SWAP
  sXᶠ c = trans (slideᶠ c sX) (front _ (refl' (Eq.sym (↑ᶠ X c))))

  sX↑ᶠ : (c : F) → (₂₊ n) ⊢ SWAP • (X ^ᶠ c) ↑ ≈ X ^ᶠ c • SWAP
  sX↑ᶠ c = trans (back _ (refl' (↑ᶠ X c))) (slideᶠ c (sym (ax swap-X)))

  Xᶠ∥X↑ᶠ : (c d : F) → (₂₊ n) ⊢ X ^ᶠ c • (X ^ᶠ d) ↑ ≈ (X ^ᶠ d) ↑ • X ^ᶠ c
  Xᶠ∥X↑ᶠ c d = trans (back _ (refl' (↑ᶠ X d)))
                 (trans (Pow.pow-comm₂ (₂₊ n) (toℕ c) (toℕ d) X∥X↑) (front _ (refl' (Eq.sym (↑ᶠ X d)))))

------------------------------------------------------------------------
-- Translations

-- x ↦ x + b.
Xc : Vec F n → Circuit n
Xc []      = ε
Xc (c ∷ b) = X ^ᶠ c • Xc b ↑

-- How a linear generator transforms a translation: b ↦ Y b.
infixl 5 _⋆ˣ_
_⋆ˣ_ : Vec F n → LGen n → Vec F n
(c ∷ b)     ⋆ˣ (y ↥ₗ) = c ∷ (b ⋆ˣ y)
(c ∷ b)     ⋆ˣ mul x  = c * proj₁ x ∷ b
(c ∷ d ∷ b) ⋆ˣ cx     = c + d ∷ d ∷ b
(c ∷ d ∷ b) ⋆ˣ sw     = d ∷ c ∷ b

-- A word, its last letter acting first.
infixl 5 _⋆ˣ*_
_⋆ˣ*_ : Vec F n → Word (LGen n) → Vec F n
b ⋆ˣ* [ y ]ʷ  = b ⋆ˣ y
b ⋆ˣ* ε       = b
b ⋆ˣ* (w • u) = b ⋆ˣ* u ⋆ˣ* w

X-push : (y : LGen n) (b : Vec F n) → n ⊢ [ ι y ]ʷ • Xc b ≈ Xc (b ⋆ˣ y) • [ ι y ]ʷ
X-push {₁₊ n} (y ↥ₗ) (c ∷ b) = begin
  Y ↑ • X ^ᶠ c • Xc b ↑                    ≈⟨ trans (sym assoc) (trans (front _ y∥X) assoc) ⟩
  X ^ᶠ c • Y ↑ • Xc b ↑                    ≈⟨ back _ (lift (X-push y b)) ⟩
  X ^ᶠ c • Xc (b ⋆ˣ y) ↑ • Y ↑             ≈⟨ sym assoc ⟩
  (X ^ᶠ c • Xc (b ⋆ˣ y) ↑) • Y ↑           ∎
  where
  open Width (₁₊ n)
  Y = [ ι y ]ʷ
  y∥X : (₁₊ n) ⊢ Y ↑ • X ^ᶠ c ≈ X ^ᶠ c • Y ↑
  y∥X = sym (Pow.pow-comm (₁₊ n) (toℕ c) (sym (comm-gate₁-w↑ X-gate Y)))
X-push {₁₊ n} (mul x) (c ∷ b) = begin
  M⟨ x ⟩ • X ^ᶠ c • Xc b ↑                 ≈⟨ trans (sym assoc) (trans (front _ (M-Xᶠ x c)) assoc) ⟩
  X ^ᶠ (c * proj₁ x) • M⟨ x ⟩ • Xc b ↑     ≈⟨ back _ (sym (comm-gate₁-w↑ (M-gate (proj₁ x) (proj₂ x)) (Xc b))) ⟩
  X ^ᶠ (c * proj₁ x) • Xc b ↑ • M⟨ x ⟩     ≈⟨ sym assoc ⟩
  (X ^ᶠ (c * proj₁ x) • Xc b ↑) • M⟨ x ⟩   ∎
  where open Width (₁₊ n)
X-push {₂₊ n} cx (c ∷ d ∷ b) = begin
  CX • X ^ᶠ c • (X ^ᶠ d) ↑ • B
    ≈⟨ trans (sym assoc) (trans (front _ (CX-Xᶠ c)) assoc) ⟩
  X ^ᶠ c • CX • (X ^ᶠ d) ↑ • B
    ≈⟨ back _ (trans (sym assoc) (front _ (CX-X↑ᶠ d))) ⟩
  X ^ᶠ c • ((X ^ᶠ d • (X ^ᶠ d) ↑) • CX) • B
    ≈⟨ back _ (trans assoc (trans assoc (back _ (back _ (sym (comm-gate₂-w↑↑ CX-gate (Xc b))))))) ⟩
  X ^ᶠ c • X ^ᶠ d • (X ^ᶠ d) ↑ • B • CX
    ≈⟨ trans (sym assoc) (front _ (Pow.Order.^ᶠ-+ (₂₊ n) X-order c d)) ⟩
  X ^ᶠ (c + d) • (X ^ᶠ d) ↑ • B • CX
    ≈⟨ back _ (sym assoc) ⟩
  X ^ᶠ (c + d) • ((X ^ᶠ d) ↑ • B) • CX
    ≈⟨ sym assoc ⟩
  (X ^ᶠ (c + d) • (X ^ᶠ d) ↑ • B) • CX ∎
  where
  open Width (₂₊ n)
  B = Xc b ↑ ↑
X-push {₂₊ n} sw (c ∷ d ∷ b) = begin
  SWAP • X ^ᶠ c • (X ^ᶠ d) ↑ • B
    ≈⟨ trans (sym assoc) (trans (front _ (sXᶠ c)) assoc) ⟩
  (X ^ᶠ c) ↑ • SWAP • (X ^ᶠ d) ↑ • B
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (sX↑ᶠ d)) assoc)) ⟩
  (X ^ᶠ c) ↑ • X ^ᶠ d • SWAP • B
    ≈⟨ back _ (back _ (sym (comm-gate₂-w↑↑ SWAP-gate (Xc b)))) ⟩
  (X ^ᶠ c) ↑ • X ^ᶠ d • B • SWAP
    ≈⟨ trans (sym assoc) (trans (front _ (sym (Xᶠ∥X↑ᶠ d c))) assoc) ⟩
  X ^ᶠ d • (X ^ᶠ c) ↑ • B • SWAP
    ≈⟨ back _ (sym assoc) ⟩
  X ^ᶠ d • ((X ^ᶠ c) ↑ • B) • SWAP
    ≈⟨ sym assoc ⟩
  (X ^ᶠ d • (X ^ᶠ c) ↑ • B) • SWAP ∎
  where
  open Width (₂₊ n)
  B = Xc b ↑ ↑

-- A linear word.
X-push* : (L : Word (LGen n)) (b : Vec F n) → n ⊢ ⌊ L ⌋ • Xc b ≈ Xc (b ⋆ˣ* L) • ⌊ L ⌋
X-push* [ y ]ʷ b  = X-push y b
X-push* ε b = Width.trans Width.left-unit (Width.sym Width.right-unit)
X-push* {n} (L • L') b = begin
  (⌊ L ⌋ • ⌊ L' ⌋) • Xc b                ≈⟨ trans assoc (back _ (X-push* L' b)) ⟩
  ⌊ L ⌋ • Xc (b ⋆ˣ* L') • ⌊ L' ⌋         ≈⟨ trans (sym assoc) (front _ (X-push* L (b ⋆ˣ* L'))) ⟩
  (Xc (b ⋆ˣ* L' ⋆ˣ* L) • ⌊ L ⌋) • ⌊ L' ⌋ ≈⟨ assoc ⟩
  Xc (b ⋆ˣ* L' ⋆ˣ* L) • ⌊ L ⌋ • ⌊ L' ⌋   ∎
  where open Width n

-- Translations add.
Xc-add : (b b' : Vec F n) → n ⊢ Xc b • Xc b' ≈ Xc (zipWith _+_ b b')
Xc-add [] [] = Width.left-unit
Xc-add {₁₊ n} (c ∷ b) (c' ∷ b') = begin
  (X ^ᶠ c • Xc b ↑) • X ^ᶠ c' • Xc b' ↑       ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  X ^ᶠ c • (Xc b ↑ • X ^ᶠ c') • Xc b' ↑       ≈⟨ back _ (front _ (sym (Pow.pow-comm (₁₊ n) (toℕ c') (sym (comm-gate₁-w↑ X-gate (Xc b)))))) ⟩
  X ^ᶠ c • (X ^ᶠ c' • Xc b ↑) • Xc b' ↑       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (X ^ᶠ c • X ^ᶠ c') • Xc b ↑ • Xc b' ↑       ≈⟨ cong (Pow.Order.^ᶠ-+ (₁₊ n) X-order c c') (lift (Xc-add b b')) ⟩
  X ^ᶠ (c + c') • Xc (zipWith _+_ b b') ↑     ∎
  where open Width (₁₊ n)

Xc-zero : n ⊢ Xc (0ᵛ {n}) ≈ ε
Xc-zero {zero}  = Width.refl
Xc-zero {suc n} = trans left-unit (lift Xc-zero)
  where open Width (₁₊ n)
