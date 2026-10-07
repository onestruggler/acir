------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: the step lemmas, and the decomposition of
-- every linear circuit
--
-- A generator meeting a row representative is absorbed into the
-- representative of the transformed row, at the price of letters of
-- the row stabiliser, emitted to the left:
--
--     r ℓ • y ≈ ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y)          (r-step)
--
-- On a big row R w • M_a a generator on the upper wires passes the
-- fan-in (Linear.Fan), CX adds to its first label, a multiplier
-- multiplies a, and SWAP meets the big cell (Linear.Two); on a small
-- row SWAP • r ℓ ↑ a generator on the upper wires is the step one
-- level down, and those on the bottom wires meet the two-level
-- gadget.  The fan-out then absorbs the letters (push-sound), and
-- every linear circuit is
--
--     W ↑ • col v • r ℓ                          (decompose)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Steps
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; _⁻¹ᶠ ; _⁻¹* ; _⊛_ ; 1* ; -1* ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Two p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letters of the level below, past SWAP

liftsw-comm : (k : Word (KLet (₁₊ n))) → (₂₊ n) ⊢ SWAP • ⟪ k ⟫ ↑ ≈ ⟪ lift-sw k ⟫ • SWAP
liftsw-comm {n} [ kup L ]ʷ =
  trans (sym (comm-gate₂-w↑↑ SWAP-gate ⌊ L ⌋)) (front _ (refl' (Eq.cong _↑ (Eq.sym (⌊↑ₗ⌋ L)))))
  where open Width (₂₊ n)
liftsw-comm {₁₊ n} [ kcol c ]ʷ = begin
  SWAP • (CXʳ ^ᶠ c) ↑                      ≈⟨ back _ (refl' (↑ᶠ CXʳ c)) ⟩
  SWAP • (CXʳ ↑) ^ᶠ c                      ≈⟨ slideᶠ c sCXʳ↑ ⟩
  CX₀₂ ^ᶠ c • SWAP                         ≈⟨ front _ (sym (conjᶠ SWAP↑² tCXʳ c)) ⟩
  (SWAP ↑ • CXʳ ^ᶠ c • SWAP ↑) • SWAP      ∎
  where open Width (₃₊ n)
liftsw-comm {n} ε       = Width.slide-ε (₂₊ n)
liftsw-comm {n} (w • v) = Width.slide (₂₊ n) (liftsw-comm w) (liftsw-comm v)

------------------------------------------------------------------------
-- The step lemmas

private
  -- A gadget followed by the rest one wire up, past a generator one
  -- wire up.
  up-step : ∀ {g : Circuit (₂₊ n)} {ρ ρ' : Circuit (₁₊ n)} {y : Gen (₁₊ n)}
              {K : Circuit (₁₊ n)} {K' : Circuit (₂₊ n)} →
            (₁₊ n) ⊢ ρ • [ y ]ʷ ≈ K • ρ' →
            (₂₊ n) ⊢ g • K ↑ ≈ K' • g →
            (₂₊ n) ⊢ (g • ρ ↑) • [ y ↥ ]ʷ ≈ K' • g • ρ' ↑
  up-step {n} {g} {ρ} {ρ'} {y} {K} {K'} e c = begin
    (g • ρ ↑) • [ y ↥ ]ʷ     ≈⟨ assoc ⟩
    g • (ρ • [ y ]ʷ) ↑       ≈⟨ back g (lift e) ⟩
    g • (K • ρ') ↑           ≈⟨ sym assoc ⟩
    (g • K ↑) • ρ' ↑         ≈⟨ front _ c ⟩
    (K' • g) • ρ' ↑          ≈⟨ assoc ⟩
    K' • g • ρ' ↑            ∎
    where open Width (₂₊ n)

  -- An involution conjugating three factors.
  split-conj₃ : ∀ {m} {g a b c : Circuit m} → m ⊢ g • g ≈ ε →
                m ⊢ g • (a • b • c) • g ≈ (g • a • g) • (g • b • g) • (g • c • g)
  split-conj₃ {m} gg = trans (split-conj gg) (back _ (split-conj gg))
    where open Width m

  -- The fan-in on wires ≥ 2 past the reversed addition.
  R₀-CXʳ : (w : Vec F n) (i : F) →
           (₂₊ n) ⊢ R₀ w • CXʳ ^ᶠ i ≈ CXʳ ^ᶠ i • R (negs i w) ↑ • R₀ w
  R₀-CXʳ {n} w i = begin
    (SWAP • R w ↑ • SWAP) • CXʳ ^ᶠ i
      ≈⟨ back _ (sym (conjᶠ ss sCX i)) ⟩
    (SWAP • R w ↑ • SWAP) • SWAP • CX ^ᶠ i • SWAP
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    SWAP • R w ↑ • (SWAP • SWAP) • CX ^ᶠ i • SWAP
      ≈⟨ back _ (back _ (trans (front _ ss) left-unit)) ⟩
    SWAP • R w ↑ • CX ^ᶠ i • SWAP
      ≈⟨ back _ (trans (sym assoc) (front _ (R-up-CX w i))) ⟩
    SWAP • (CX ^ᶠ i • R₀ (negs i w) • R w ↑) • SWAP
      ≈⟨ split-conj₃ ss ⟩
    (SWAP • CX ^ᶠ i • SWAP) • (SWAP • R₀ (negs i w) • SWAP) • (SWAP • R w ↑ • SWAP)
      ≈⟨ cong (conjᶠ ss sCX i) (front _ undo) ⟩
    CXʳ ^ᶠ i • R (negs i w) ↑ • R₀ w ∎
    where
    open Width (₂₊ n)
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order
    undo : (₂₊ n) ⊢ SWAP • R₀ (negs i w) • SWAP ≈ R (negs i w) ↑
    undo = trans (by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl)
                 (trans (cancel-in ss _) (cancel-at ss _))

r-step : (ℓ : NZ n) (y : LGen n) → n ⊢ r ℓ • [ ι y ]ʷ ≈ ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y)
r-step {₁₊ n} (big a w) (y ↥ₗ) = begin
  (R w • M⟨ a ⟩) • Y ↑                  ≈⟨ trans assoc (back _ (sym (comm-gate₁-w↑ (M-gate (proj₁ a) (proj₂ a)) Y))) ⟩
  R w • Y ↑ • M⟨ a ⟩                    ≈⟨ trans (sym assoc) (trans (front _ (R-push w y)) assoc) ⟩
  Y ↑ • R (w ⋆ᴿ y) • M⟨ a ⟩             ∎
  where
  open Width (₁₊ n)
  Y = ⌊ [ y ]ʷ ⌋
r-step (small ℓ) (y ↥ₗ) = up-step (r-step ℓ y) (liftsw-comm (rk ℓ y))
r-step {₁₊ n} (big a w) (mul x) = begin
  (R w • M⟨ a ⟩) • M⟨ x ⟩               ≈⟨ trans assoc (back _ (ax (ax2 x a))) ⟩
  R w • M⟨ x ⊛ a ⟩                      ≈⟨ sym left-unit ⟩
  ε • R w • M⟨ x ⊛ a ⟩                  ∎
  where open Width (₁₊ n)
r-step {₂₊ n} (small ℓ) (mul x) =
  pass (sM x) (comm-gate₁-w↑ (M-gate (proj₁ x) (proj₂ x)) (r ℓ))
r-step {₂₊ n} (big a (c ∷ w)) cx = begin
  (R (c ∷ w) • M⟨ a ⟩) • CX             ≈⟨ trans assoc (back _ (M-CX a)) ⟩
  R (c ∷ w) • CX ^ᶠ proj₁ a • M⟨ a ⟩    ≈⟨ trans (sym assoc) (front _ (R-add c (proj₁ a) w)) ⟩
  R (c + proj₁ a ∷ w) • M⟨ a ⟩          ≈⟨ sym left-unit ⟩
  ε • R (c + proj₁ a ∷ w) • M⟨ a ⟩      ∎
  where open Width (₂₊ n)
r-step {₂₊ n} (small (big b w)) cx = begin
  (SWAP • R w ↑ • M⟨ b ⟩ ↑) • CX
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  SWAP • R w ↑ • M⟨ b ⟩ ↑ • CX
    ≈⟨ back _ (back _ (trans (M↑-CXᶠ b 1F) (front _ (OA.^ᶠ-≡ (FR.*-identityˡ i))))) ⟩
  SWAP • R w ↑ • CX ^ᶠ i • M⟨ b ⟩ ↑
    ≈⟨ back _ (trans (sym assoc) (front _ (R-up-CX w i))) ⟩
  SWAP • (CX ^ᶠ i • R₀ u • R w ↑) • M⟨ b ⟩ ↑
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (SWAP • CX ^ᶠ i) • R₀ u • R w ↑ • M⟨ b ⟩ ↑
    ≈⟨ trans (front _ (slideᶠ i sCX)) assoc ⟩
  CXʳ ^ᶠ i • SWAP • R₀ u • R w ↑ • M⟨ b ⟩ ↑
    ≈⟨ back _ (trans (sym assoc) (front _ (cancel-in ss _))) ⟩
  CXʳ ^ᶠ i • ((R u ↑ • SWAP) • R w ↑ • M⟨ b ⟩ ↑)
    ≈⟨ back _ (trans assoc (front _ (refl' (Eq.cong _↑ (Eq.sym (⌊Rʷ⌋ u)))))) ⟩
  CXʳ ^ᶠ i • ⌊ Rʷ u ⌋ ↑ • SWAP • R w ↑ • M⟨ b ⟩ ↑
    ≈⟨ sym assoc ⟩
  (CXʳ ^ᶠ i • ⌊ Rʷ u ⌋ ↑) • SWAP • R w ↑ • M⟨ b ⟩ ↑ ∎
  where
  open Width (₂₊ n)
  module OA = Pow.Order (₂₊ n) {CX} CX-order
  i = proj₁ b ⁻¹ᶠ
  u = negs i w
  ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
  ss = ax swap-order
r-step {₃₊ n} (small (small ℓ)) cx =
  pass sCX₂₀ (pass tCX (comm-gate₂-w↑↑ CX-gate (r ℓ)))
r-step {₂₊ n} (big a (c ∷ w)) sw with c ≟ 0F
... | yes refl = begin
  (((SWAP • R w ↑ • SWAP) • ε) • M⟨ a ⟩) • SWAP
    ≈⟨ front _ (front _ right-unit) ⟩
  ((SWAP • R w ↑ • SWAP) • M⟨ a ⟩) • SWAP
    ≈⟨ by-passoc (((□ • □ • □) • □) • □) (□ • □ • (□ • □ • □)) Eq.refl ⟩
  SWAP • R w ↑ • (SWAP • M⟨ a ⟩ • SWAP)
    ≈⟨ back _ (back _ (Involution.conj← (ax swap-order) (sM a))) ⟩
  SWAP • R w ↑ • M⟨ a ⟩ ↑
    ≈⟨ sym left-unit ⟩
  ε • SWAP • R w ↑ • M⟨ a ⟩ ↑ ∎
  where open Width (₂₊ n)
... | no nc = begin
  (((SWAP • R w ↑ • SWAP) • CX ^ᶠ c) • M⟨ a ⟩) • SWAP
    ≈⟨ by-passoc (((□ • □) • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  R₀ w • CX ^ᶠ c • M⟨ a ⟩ • SWAP
    ≈⟨ back _ (bruhat c* a) ⟩
  R₀ w • CXʳ ^ᶠ i • M⟨ u ⟩ ↑ • CX ^ᶠ proj₁ a • M⟨ c* ⟩
    ≈⟨ trans (sym assoc) (front _ (R₀-CXʳ w i)) ⟩
  (CXʳ ^ᶠ i • R (negs i w) ↑ • R₀ w) • M⟨ u ⟩ ↑ • CX ^ᶠ proj₁ a • M⟨ c* ⟩
    ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  CXʳ ^ᶠ i • R (negs i w) ↑ • (R₀ w • M⟨ u ⟩ ↑) • CX ^ᶠ proj₁ a • M⟨ c* ⟩
    ≈⟨ back _ (back _ (front _ (conj-M↑ (R w) u))) ⟩
  CXʳ ^ᶠ i • R (negs i w) ↑ • (M⟨ u ⟩ ↑ • R₀ w) • CX ^ᶠ proj₁ a • M⟨ c* ⟩
    ≈⟨ back _ (front _ (refl' (Eq.cong _↑ (Eq.sym (⌊Rʷ⌋ (negs i w)))))) ⟩
  CXʳ ^ᶠ i • ⌊ Rʷ (negs i w) ⌋ ↑ • (M⟨ u ⟩ ↑ • R₀ w) • CX ^ᶠ proj₁ a • M⟨ c* ⟩
    ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • (□ • □) • □) Eq.refl ⟩
  (CXʳ ^ᶠ i • ⌊ Rʷ (negs i w) ⌋ ↑ • M⟨ u ⟩ ↑) • (R₀ w • CX ^ᶠ proj₁ a) • M⟨ c* ⟩ ∎
  where
  open Width (₂₊ n)
  c* : F*
  c* = c , nc
  i = c ⁻¹ᶠ
  u = a ⊛ (-1* ⊛ c* ⁻¹*)
r-step {₂₊ n} (small (big b w)) sw = begin
  (SWAP • R w ↑ • M⟨ b ⟩ ↑) • SWAP
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  SWAP • R w ↑ • M⟨ b ⟩ ↑ • SWAP
    ≈⟨ back _ (back _ (sym (sM b))) ⟩
  SWAP • R w ↑ • SWAP • M⟨ b ⟩
    ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
  (SWAP • R w ↑ • SWAP) • M⟨ b ⟩
    ≈⟨ front _ (sym right-unit) ⟩
  ((SWAP • R w ↑ • SWAP) • ε) • M⟨ b ⟩
    ≈⟨ sym left-unit ⟩
  ε • ((SWAP • R w ↑ • SWAP) • ε) • M⟨ b ⟩ ∎
  where open Width (₂₊ n)
r-step {₃₊ n} (small (small ℓ)) sw = begin
  (SWAP • SWAP ↑ • r ℓ ↑ ↑) • SWAP
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  SWAP • SWAP ↑ • r ℓ ↑ ↑ • SWAP
    ≈⟨ back _ (back _ (comm-gate₂-w↑↑ SWAP-gate (r ℓ))) ⟩
  SWAP • SWAP ↑ • SWAP • r ℓ ↑ ↑
    ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) (front _ (ax swap-braid)) ⟩
  (SWAP ↑ • SWAP • SWAP ↑) • r ℓ ↑ ↑
    ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  SWAP ↑ • SWAP • SWAP ↑ • r ℓ ↑ ↑ ∎
  where open Width (₃₊ n)

------------------------------------------------------------------------
-- The fan-out absorbs the row's letters

push-sound : (v : Vec F n) (k : Word (KLet (₁₊ n))) →
             (₁₊ n) ⊢ col v • ⟪ k ⟫ ≈ proj₁ (push v k) ↑ • col (proj₂ (push v k))
push-sound v [ kup L ]ʷ = col-push* v L
push-sound {₁₊ n} (d ∷ v) [ kcol c ]ʷ = trans (col-add d c v) (sym left-unit)
  where open Width (₂₊ n)
push-sound {n} v ε = trans right-unit (sym left-unit)
  where open Width (₁₊ n)
push-sound {n} v (w • u) = begin
  col v • ⟪ w ⟫ • ⟪ u ⟫               ≈⟨ sym assoc ⟩
  (col v • ⟪ w ⟫) • ⟪ u ⟫             ≈⟨ front _ (push-sound v w) ⟩
  (W₁ ↑ • col v₁) • ⟪ u ⟫             ≈⟨ assoc ⟩
  W₁ ↑ • col v₁ • ⟪ u ⟫               ≈⟨ back _ (push-sound v₁ u) ⟩
  W₁ ↑ • W₂ ↑ • col v₂                ≈⟨ sym assoc ⟩
  (W₁ • W₂) ↑ • col v₂                ∎
  where
  open Width (₁₊ n)
  W₁ = proj₁ (push v w)
  v₁ = proj₂ (push v w)
  W₂ = proj₁ (push v₁ u)
  v₂ = proj₂ (push v₁ u)

------------------------------------------------------------------------
-- The normal form of a linear circuit

record LNF (n : ℕ) : Set where
  constructor ⟨_,_,_⟩
  field
    upper  : Circuit n
    column : Vec F n
    form   : NZ (₁₊ n)

⌜_⌝ : LNF n → Circuit (₁₊ n)
⌜ ⟨ W , v , ℓ ⟩ ⌝ = W ↑ • col v • r ℓ

step : LNF n → LGen (₁₊ n) → LNF n
step ⟨ W , v , ℓ ⟩ y =
  ⟨ W • proj₁ (push v (rk ℓ y)) , proj₂ (push v (rk ℓ y)) , ℓ ⋆ y ⟩

step-sound : (N : LNF n) (y : LGen (₁₊ n)) →
             (₁₊ n) ⊢ ⌜ N ⌝ • [ ι y ]ʷ ≈ ⌜ step N y ⌝
step-sound {n} ⟨ W , v , ℓ ⟩ y = begin
  (W ↑ • col v • r ℓ) • [ ι y ]ʷ           ≈⟨ assoc ⟩
  W ↑ • (col v • r ℓ) • [ ι y ]ʷ           ≈⟨ back _ assoc ⟩
  W ↑ • col v • r ℓ • [ ι y ]ʷ             ≈⟨ back _ (back _ (r-step ℓ y)) ⟩
  W ↑ • col v • ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y)     ≈⟨ back _ (sym assoc) ⟩
  W ↑ • (col v • ⟪ rk ℓ y ⟫) • r (ℓ ⋆ y)   ≈⟨ back _ (front _ (push-sound v (rk ℓ y))) ⟩
  W ↑ • (W' ↑ • col v') • r (ℓ ⋆ y)        ≈⟨ back _ assoc ⟩
  W ↑ • W' ↑ • col v' • r (ℓ ⋆ y)          ≈⟨ sym assoc ⟩
  (W • W') ↑ • col v' • r (ℓ ⋆ y)          ∎
  where
  open Width (₁₊ n)
  W' = proj₁ (push v (rk ℓ y))
  v' = proj₂ (push v (rk ℓ y))

run : LNF n → Word (LGen (₁₊ n)) → LNF n
run N [ y ]ʷ  = step N y
run N ε       = N
run N (w • v) = run (run N w) v

run-sound : (N : LNF n) (L : Word (LGen (₁₊ n))) →
            (₁₊ n) ⊢ ⌜ N ⌝ • ⌊ L ⌋ ≈ ⌜ run N L ⌝
run-sound N [ y ]ʷ = step-sound N y
run-sound {n} N ε = right-unit
  where open Width (₁₊ n)
run-sound {n} N (w • v) = begin
  ⌜ N ⌝ • ⌊ w ⌋ • ⌊ v ⌋          ≈⟨ sym assoc ⟩
  (⌜ N ⌝ • ⌊ w ⌋) • ⌊ v ⌋        ≈⟨ front _ (run-sound N w) ⟩
  ⌜ run N w ⌝ • ⌊ v ⌋            ≈⟨ run-sound (run N w) v ⟩
  ⌜ run (run N w) v ⌝            ∎
  where open Width (₁₊ n)

-- The normal form of the empty circuit, and of any linear circuit.
nf₀ : LNF n
nf₀ = ⟨ ε , 0ᵛ , big 1* 0ᵛ ⟩

nf₀-sound : (₁₊ n) ⊢ ⌜ nf₀ {n} ⌝ ≈ ε
nf₀-sound {n} = begin
  ε • col 0ᵛ • R 0ᵛ • M⟨ 1* ⟩    ≈⟨ left-unit ⟩
  col 0ᵛ • R 0ᵛ • M⟨ 1* ⟩        ≈⟨ cong col-zero (cong R-zero (ax ax1)) ⟩
  ε • ε • ε                      ≈⟨ trans left-unit left-unit ⟩
  ε                              ∎
  where open Width (₁₊ n)

lnf : Word (LGen (₁₊ n)) → LNF n
lnf = run nf₀

decompose : (L : Word (LGen (₁₊ n))) → (₁₊ n) ⊢ ⌊ L ⌋ ≈ ⌜ lnf L ⌝
decompose {n} L = begin
  ⌊ L ⌋                ≈⟨ sym left-unit ⟩
  ε • ⌊ L ⌋            ≈⟨ front _ (sym nf₀-sound) ⟩
  ⌜ nf₀ ⌝ • ⌊ L ⌋      ≈⟨ run-sound nf₀ L ⟩
  ⌜ run nf₀ L ⌝        ∎
  where open Width (₁₊ n)
