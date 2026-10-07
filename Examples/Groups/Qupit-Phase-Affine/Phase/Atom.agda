------------------------------------------------------------------------
-- Presentations of groups
--
-- Atoms: a one-wire phase gate conjugated by a row
--
-- For a gate G on wire 0 that commutes with CXʳ (G on its control) and
-- that SWAP moves up a wire, and a row ℓ,
--
--     A ℓ = (r ℓ)⁻¹ • G • r ℓ
--
-- is G applied to the label ℓ·x that r ℓ writes on wire 0.  A linear
-- generator y carries it to the atom of ℓ ⋆ y (A-step): r ℓ • y is
-- ⟪ k ⟫ • r (ℓ ⋆ y) for letters k that keep wire 0, which G passes.
-- Conjugating by a whole linear word transports the row along the word
-- (A-conj), an atom of a row with x₀-coefficient 0 is an atom one wire
-- up (A-small), and a translation shifts the gate G it conjugates
-- (A-X).  A gate g that commutes with r ℓ X (r ℓ)⁻¹ makes the atom of ℓ
-- commute with X (conj-into), which is how atoms are shown to commute.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Atom
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime using (F)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Commute p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Steps p-2 p-prime lv using (r-step)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (Xc ; _⋆ˣ*_ ; X-push*)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Inverses

-- The inverse of a word one wire up.
⁻¹-↑ : (w : Circuit n) → (w ↑) ⁻¹ ≡ (w ⁻¹) ↑
⁻¹-↑ [ g ]ʷ  = Eq.refl
⁻¹-↑ ε       = Eq.refl
⁻¹-↑ (w • v) = Eq.cong₂ _•_ (⁻¹-↑ v) (⁻¹-↑ w)

module _ {m : ℕ} where

  open Width m

  -- u • w ≈ w' • v read across an invertible word.
  flip⁻¹ : {u w v w' : Circuit m} → u • w ≈ w' • v → w' ⁻¹ • u ≈ v • w ⁻¹
  flip⁻¹ {u} {w} {v} {w'} e = begin
    w' ⁻¹ • u                    ≈⟨ back _ (sym (trans (back _ (Inv.inverseʳ m)) right-unit)) ⟩
    w' ⁻¹ • u • w • w ⁻¹         ≈⟨ back _ (trans (sym assoc) (front _ e)) ⟩
    w' ⁻¹ • (w' • v) • w ⁻¹      ≈⟨ trans (sym assoc) (front _ (trans (sym assoc) (trans (front _ (Inv.inverseˡ m)) left-unit))) ⟩
    v • w ⁻¹                     ∎

  -- A word commuting with a conjugate, conjugated back.
  conj-comm : (g ρ X : Circuit m) → m ⊢ g ∥ (ρ • X • ρ ⁻¹) → m ⊢ (ρ ⁻¹ • g • ρ) ∥ X
  conj-comm g ρ X c = begin
    (ρ ⁻¹ • g • ρ) • X
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    ρ ⁻¹ • g • ρ • X
      ≈⟨ back _ (back _ (sym (trans (back _ (Inv.inverseˡ m)) right-unit))) ⟩
    ρ ⁻¹ • g • (ρ • X) • ρ ⁻¹ • ρ
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • (□ • (□ • □ • □)) • □) Eq.refl ⟩
    ρ ⁻¹ • (g • (ρ • X • ρ ⁻¹)) • ρ
      ≈⟨ back _ (front _ c) ⟩
    ρ ⁻¹ • ((ρ • X • ρ ⁻¹) • g) • ρ
      ≈⟨ by-passoc (□ • ((□ • □ • □) • □) • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (ρ ⁻¹ • ρ) • X • ρ ⁻¹ • g • ρ
      ≈⟨ trans (front _ (Inv.inverseˡ m)) left-unit ⟩
    X • ρ ⁻¹ • g • ρ ∎

------------------------------------------------------------------------
-- Atoms of a gate on wire 0

module Atoms
  (g : Gate 1)
  (G-CXʳ : ∀ {n} → (₂₊ n) ⊢ [ gate₁ g ]ʷ • CXʳ ≈ CXʳ • [ gate₁ g ]ʷ)
  (G-swap : ∀ {n} → (₂₊ n) ⊢ [ gate₁ g ]ʷ • SWAP ≈ SWAP • [ gate₁ g ]ʷ ↑)
  where

  G : Circuit (₁₊ n)
  G = [ gate₁ g ]ʷ

  -- G passes the letters of a step, which keep wire 0.
  G-up : (w : Circuit n) → (₁₊ n) ⊢ G ∥ (w ↑)
  G-up w = Width.sym (comm-gate₁-w↑ g w)

  G-κ : (k : KLet (₁₊ n)) → (₁₊ n) ⊢ G ∥ κ k
  G-κ (kup L)  = G-up ⌊ L ⌋
  G-κ (kcol c) = ∥-sym (∥-^ᶠ c (∥-sym G-CXʳ))

  G-⟪⟫ : (k : Word (KLet (₁₊ n))) → (₁₊ n) ⊢ G ∥ ⟪ k ⟫
  G-⟪⟫ [ k ]ʷ  = G-κ k
  G-⟪⟫ ε       = Width.trans Width.right-unit (Width.sym Width.left-unit)
  G-⟪⟫ (k • l) = ∥-• (G-⟪⟫ k) (G-⟪⟫ l)

  A : NZ (₁₊ n) → Circuit (₁₊ n)
  A ℓ = r ℓ ⁻¹ • G • r ℓ

  A-≡ : {ℓ ℓ' : NZ (₁₊ n)} → row ℓ ≡ row ℓ' → (₁₊ n) ⊢ A ℓ ≈ A ℓ'
  A-≡ {n} {ℓ} {ℓ'} e = Width.refl' (₁₊ n) (Eq.cong (λ q → q ⁻¹ • G • q) (row-r ℓ ℓ' e))

  -- A linear generator transports the row.
  A-step : (ℓ : NZ (₁₊ n)) (y : LGen (₁₊ n)) → (₁₊ n) ⊢ A ℓ • [ ι y ]ʷ ≈ [ ι y ]ʷ • A (ℓ ⋆ y)
  A-step {n} ℓ y = begin
    (ρ ⁻¹ • G • ρ) • Y                   ≈⟨ trans assoc (back _ (trans assoc (back _ (r-step ℓ y)))) ⟩
    ρ ⁻¹ • G • K • ρ'                    ≈⟨ back _ (trans (sym assoc) (trans (front _ (G-⟪⟫ (rk ℓ y))) assoc)) ⟩
    ρ ⁻¹ • K • G • ρ'                    ≈⟨ trans (sym assoc) (front _ (flip⁻¹ (sym (r-step ℓ y)))) ⟩
    (Y • ρ' ⁻¹) • G • ρ'                 ≈⟨ assoc ⟩
    Y • ρ' ⁻¹ • G • ρ'                   ∎
    where
    open Width (₁₊ n)
    ρ ρ' K Y : Circuit (₁₊ n)
    ρ  = r ℓ
    ρ' = r (ℓ ⋆ y)
    K  = ⟪ rk ℓ y ⟫
    Y  = [ ι y ]ʷ

  A-steps : (ℓ : NZ (₁₊ n)) (L : Word (LGen (₁₊ n))) → (₁₊ n) ⊢ A ℓ • ⌊ L ⌋ ≈ ⌊ L ⌋ • A (ℓ ⋆* L)
  A-steps ℓ [ y ]ʷ = A-step ℓ y
  A-steps {n} ℓ ε  = trans right-unit (sym left-unit)
    where open Width (₁₊ n)
  A-steps {n} ℓ (L • M) = begin
    A ℓ • ⌊ L ⌋ • ⌊ M ⌋                  ≈⟨ trans (sym assoc) (trans (front _ (A-steps ℓ L)) assoc) ⟩
    ⌊ L ⌋ • A (ℓ ⋆* L) • ⌊ M ⌋           ≈⟨ back _ (A-steps (ℓ ⋆* L) M) ⟩
    ⌊ L ⌋ • ⌊ M ⌋ • A (ℓ ⋆* L ⋆* M)      ≈⟨ sym assoc ⟩
    (⌊ L ⌋ • ⌊ M ⌋) • A (ℓ ⋆* L ⋆* M)    ∎
    where open Width (₁₊ n)

  -- Conjugating by a linear word.
  A-conj : (ℓ : NZ (₁₊ n)) (L : Word (LGen (₁₊ n))) → (₁₊ n) ⊢ ⌊ L ⌋ ⁻¹ • A ℓ • ⌊ L ⌋ ≈ A (ℓ ⋆* L)
  A-conj {n} ℓ L = trans (back _ (A-steps ℓ L)) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit))
    where open Width (₁₊ n)

  -- The atom of a row without x₀ is an atom one wire up.
  A-small : (ℓ : NZ (₁₊ n)) → (₂₊ n) ⊢ A (small ℓ) ≈ A ℓ ↑
  A-small {n} ℓ = begin
    (r ℓ ↑ ⁻¹ • SWAP) • G • SWAP • r ℓ ↑      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    r ℓ ↑ ⁻¹ • (SWAP • G • SWAP) • r ℓ ↑      ≈⟨ back _ (front _ sGs) ⟩
    r ℓ ↑ ⁻¹ • G ↑ • r ℓ ↑                    ≈⟨ front _ (refl' (⁻¹-↑ (r ℓ))) ⟩
    (r ℓ ⁻¹) ↑ • G ↑ • r ℓ ↑                  ∎
    where
    open Width (₂₊ n)
    sGs : (₂₊ n) ⊢ SWAP • G • SWAP ≈ G ↑
    sGs = trans (back _ G-swap) (trans (sym assoc) (trans (front _ (ax swap-order)) left-unit))

  -- Iterates conjugate the iterate of G.
  A-^ : (ℓ : NZ (₁₊ n)) (k : ℕ) → (₁₊ n) ⊢ A ℓ ^ k ≈ r ℓ ⁻¹ • G ^ k • r ℓ
  A-^ {n} ℓ = conj-pow (Inv.inverseˡ (₁₊ n)) (Inv.inverseʳ (₁₊ n))

  -- A translation passes the atom of a gate it passes.
  A-X : (ℓ : NZ (₁₊ n)) (b : Vec F (₁₊ n)) {D : Circuit (₁₊ n)} →
        (₁₊ n) ⊢ G • Xc (b ⋆ˣ* rL ℓ) ≈ Xc (b ⋆ˣ* rL ℓ) • G • D →
        (₁₊ n) ⊢ A ℓ • Xc b ≈ Xc b • A ℓ • (r ℓ ⁻¹ • D • r ℓ)
  A-X {n} ℓ b {D} e = begin
    (ρ ⁻¹ • G • ρ) • Xc b                ≈⟨ trans assoc (back _ (trans assoc (back _ ρXc))) ⟩
    ρ ⁻¹ • G • Xc v • ρ                  ≈⟨ back _ (trans (sym assoc) (trans (front _ e) assoc)) ⟩
    ρ ⁻¹ • Xc v • (G • D) • ρ            ≈⟨ trans (sym assoc) (front _ (flip⁻¹ (sym ρXc))) ⟩
    (Xc b • ρ ⁻¹) • (G • D) • ρ          ≈⟨ assoc ⟩
    Xc b • ρ ⁻¹ • (G • D) • ρ            ≈⟨ back _ (back _ (trans assoc (back _ (sym (trans (front _ (Inv.inverseʳ (₁₊ n))) left-unit))))) ⟩
    Xc b • ρ ⁻¹ • G • (ρ • ρ ⁻¹) • D • ρ ≈⟨ back _ (by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl) ⟩
    Xc b • (ρ ⁻¹ • G • ρ) • ρ ⁻¹ • D • ρ ∎
    where
    open Width (₁₊ n)
    ρ : Circuit (₁₊ n)
    ρ = r ℓ
    v = b ⋆ˣ* rL ℓ
    ρXc : (₁₊ n) ⊢ ρ • Xc b ≈ Xc v • ρ
    ρXc = Eq.subst (λ q → (₁₊ n) ⊢ q • Xc b ≈ Xc v • q) (⌊rL⌋ ℓ) (X-push* (rL ℓ) b)

  -- G past r ℓ X (r ℓ)⁻¹ makes the atom of ℓ commute with X.
  conj-into : (ℓ : NZ (₁₊ n)) (X : Circuit (₁₊ n)) → (₁₊ n) ⊢ G ∥ (r ℓ • X • r ℓ ⁻¹) → (₁₊ n) ⊢ A ℓ ∥ X
  conj-into ℓ X = conj-comm G (r ℓ) X

  -- r ℓ (r ℓ')⁻¹-conjugates as a linear word.
  rr⁻¹ : (ℓ ℓ' : NZ (₁₊ n)) → (₁₊ n) ⊢ r ℓ • A ℓ' • r ℓ ⁻¹ ≈ A (ℓ' ⋆* linv (rL ℓ))
  rr⁻¹ {n} ℓ ℓ' = begin
    r ℓ • A ℓ' • r ℓ ⁻¹                  ≈⟨ back _ (back _ (sym L≈)) ⟩
    r ℓ • A ℓ' • ⌊ L ⌋                   ≈⟨ back _ (A-steps ℓ' L) ⟩
    r ℓ • ⌊ L ⌋ • A (ℓ' ⋆* L)            ≈⟨ trans (sym assoc) (trans (front _ (trans (back _ L≈) (Inv.inverseʳ (₁₊ n)))) left-unit) ⟩
    A (ℓ' ⋆* L)                          ∎
    where
    open Width (₁₊ n)
    L = linv (rL ℓ)
    L≈ : (₁₊ n) ⊢ ⌊ L ⌋ ≈ r ℓ ⁻¹
    L≈ = trans (⌊linv⌋ (rL ℓ)) (refl' (Eq.cong _⁻¹ (⌊rL⌋ ℓ)))
