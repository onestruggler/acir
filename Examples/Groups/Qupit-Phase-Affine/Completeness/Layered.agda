------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness from a diagonal layer
--
-- At a phase level every circuit is a translation, a linear circuit
-- and a diagonal circuit, in that order from the output:
--
--     Xc b • ⌊ L ⌋ • ⟦ d ⟧ᵈ
--
-- given a layer of diagonal forms d that the affine generators move
-- across (lin-tr, tr-tr) and that absorb the phase generators (app).
-- Two such forms with the same operator have the same translation, the
-- same linear operator — the diagonal parts fixing every label — and
-- diagonal parts with the same phase function; so they are equal once
-- the layer's forms are determined by their phases (unique), given
-- completeness one wire down.  Each level supplies its layer and the
-- way its generators split into linear ones, translations and phases
-- (Run); completeness at every width follows by induction.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

import Examples.Groups.Qupit-Phase-Affine.Soundness as Snd

module Examples.Groups.Qupit-Phase-Affine.Completeness.Layered
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ)
  (adm : Snd.Admissible p-2 p-prime lv) where

open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; module ≡-Reasoning)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime lv
  using (X-at ; M-at ; CX-at ; SWAP-at ; Xᶠ-at)
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime lv adm
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Completeness p-2 p-prime lv adm
  using (linear-complete)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Linear circuits and translations on labels

-- A linear generator fixes 0 and picks up no phase.
gen-0 : (y : LGen n) → fn [ ι y ]ʷ 0ᵛ ≡ 0ᵛ
gen-0 cx      = Eq.trans (Eq.cong proj₁ (CX-at 0F 0F 0ᵛ)) (Eq.cong (_∷ 0F ∷ 0ᵛ) (FR.+-identityʳ 0F))
gen-0 sw      = Eq.cong proj₁ (SWAP-at 0F 0F 0ᵛ)
gen-0 (mul x) = Eq.trans (Eq.cong proj₁ (M-at (proj₁ x) (proj₂ x) 0F 0ᵛ)) (Eq.cong (_∷ 0ᵛ) (FR.zeroʳ _))
gen-0 (y ↥ₗ)  = Eq.trans (fn-↑ [ ι y ]ʷ 0F 0ᵛ) (Eq.cong (0F ∷_) (gen-0 y))

gen-ph : (y : LGen n) (x : Labels n) → ph [ ι y ]ʷ x ≡ 0F
gen-ph cx      (a ∷ b ∷ x) = Eq.cong proj₂ (CX-at a b x)
gen-ph sw      (a ∷ b ∷ x) = Eq.cong proj₂ (SWAP-at a b x)
gen-ph (mul c) (a ∷ x)     = Eq.cong proj₂ (M-at (proj₁ c) (proj₂ c) a x)
gen-ph (y ↥ₗ)  (a ∷ x)     = Eq.trans (ph-↑ [ ι y ]ʷ a x) (gen-ph y x)

lin-0 : (L : Word (LGen n)) → fn ⌊ L ⌋ 0ᵛ ≡ 0ᵛ
lin-0 [ y ]ʷ  = gen-0 y
lin-0 ε       = fn-ε 0ᵛ
lin-0 (L • M) = Eq.trans (fn-• ⌊ L ⌋ ⌊ M ⌋ 0ᵛ) (Eq.trans (Eq.cong (fn ⌊ L ⌋) (lin-0 M)) (lin-0 L))

lin-ph : (L : Word (LGen n)) (x : Labels n) → ph ⌊ L ⌋ x ≡ 0F
lin-ph [ y ]ʷ  x = gen-ph y x
lin-ph ε       x = ph-ε x
lin-ph (L • M) x = Eq.trans (ph-• ⌊ L ⌋ ⌊ M ⌋ x)
                     (Eq.trans (Eq.cong₂ _+_ (lin-ph M x) (lin-ph L (fn ⌊ M ⌋ x))) (FR.+-identityʳ 0F))

-- A translation moves 0 to its vector, and picks up no phase.
Xc-0 : (b : Vec F n) → fn (Xc b) 0ᵛ ≡ b
Xc-0 []      = fn-ε []
Xc-0 (c ∷ b) = begin
  fn (X ^ᶠ c • Xc b ↑) (0F ∷ 0ᵛ)        ≡⟨ fn-• (X ^ᶠ c) (Xc b ↑) (0F ∷ 0ᵛ) ⟩
  fn (X ^ᶠ c) (fn (Xc b ↑) (0F ∷ 0ᵛ))   ≡⟨ Eq.cong (fn (X ^ᶠ c)) (fn-↑ (Xc b) 0F 0ᵛ) ⟩
  fn (X ^ᶠ c) (0F ∷ fn (Xc b) 0ᵛ)       ≡⟨ Eq.cong (λ y → fn (X ^ᶠ c) (0F ∷ y)) (Xc-0 b) ⟩
  fn (X ^ᶠ c) (0F ∷ b)                  ≡⟨ Eq.cong proj₁ (Xᶠ-at c 0F b) ⟩
  0F + c ∷ b                            ≡⟨ Eq.cong (_∷ b) (FR.+-identityˡ c) ⟩
  c ∷ b                                 ∎
  where open ≡-Reasoning

Xc-ph : (b : Vec F n) (x : Labels n) → ph (Xc b) x ≡ 0F
Xc-ph []      [] = ph-ε []
Xc-ph (c ∷ b) (a ∷ x) = begin
  ph (X ^ᶠ c • Xc b ↑) (a ∷ x)                              ≡⟨ ph-• (X ^ᶠ c) (Xc b ↑) (a ∷ x) ⟩
  ph (Xc b ↑) (a ∷ x) + ph (X ^ᶠ c) (fn (Xc b ↑) (a ∷ x))   ≡⟨ Eq.cong₂ _+_ (Eq.trans (ph-↑ (Xc b) a x) (Xc-ph b x))
                                                                 (Eq.cong (ph (X ^ᶠ c)) (fn-↑ (Xc b) a x)) ⟩
  0F + ph (X ^ᶠ c) (a ∷ fn (Xc b) x)                        ≡⟨ Eq.cong (0F +_) (Eq.cong proj₂ (Xᶠ-at c a (fn (Xc b) x))) ⟩
  0F + 0F                                                   ≡⟨ FR.+-identityʳ 0F ⟩
  0F                                                        ∎
  where open ≡-Reasoning

-- On no wires there are no linear generators.
lin-none : (L : Word (LGen 0)) → 0 ⊢ ⌊ L ⌋ ≈ ε
lin-none [ () ]ʷ
lin-none ε       = Width.refl
lin-none (L • M) = Width.trans (Width.cong (lin-none L) (lin-none M)) Width.left-unit

------------------------------------------------------------------------
-- The generators of a level: linear ones, translations and phases

data Kind (PG : ℕ → Set) (n : ℕ) : Set where
  lin : LGen n → Kind PG n
  tr  : Vec F n → Kind PG n
  phs : PG n → Kind PG n

------------------------------------------------------------------------
-- The layered normal form, given a diagonal layer

module Layer
  (D : ℕ → Set)
  (⟦_⟧ᵈ : ∀ {n} → D n → Circuit n)
  (d₀ : ∀ {n} → D n)
  (d₀-ε : ∀ {n} → n ⊢ ⟦ d₀ {n} ⟧ᵈ ≈ ε)
  (_⋆ˡ_ : ∀ {n} → D n → LGen n → D n)
  (lin-tr : ∀ {n} (d : D n) (y : LGen n) → n ⊢ ⟦ d ⟧ᵈ • [ ι y ]ʷ ≈ [ ι y ]ʷ • ⟦ d ⋆ˡ y ⟧ᵈ)
  (_⋆ᵗ_ : ∀ {n} → D n → Vec F n → D n)
  (tr-tr : ∀ {n} (d : D n) (v : Vec F n) → n ⊢ ⟦ d ⟧ᵈ • Xc v ≈ Xc v • ⟦ d ⋆ᵗ v ⟧ᵈ)
  (PG : ℕ → Set)
  (⟦_⟧ᵖ : ∀ {n} → PG n → Circuit n)
  (app : ∀ {n} → D n → PG n → D n)
  (app-sound : ∀ {n} (d : D n) (g : PG n) → n ⊢ ⟦ d ⟧ᵈ • ⟦ g ⟧ᵖ ≈ ⟦ app d g ⟧ᵈ)
  (diag : ∀ {n} (d : D n) (x : Labels n) → fn ⟦ d ⟧ᵈ x ≡ x)
  (unique₀ : (d d' : D 0) → (∀ x → ph ⟦ d ⟧ᵈ x ≡ ph ⟦ d' ⟧ᵈ x) → 0 ⊢ ⟦ d ⟧ᵈ ≈ ⟦ d' ⟧ᵈ)
  (unique : ∀ {n} → Complete n → (d d' : D (₁₊ n)) →
            (∀ x → ph ⟦ d ⟧ᵈ x ≡ ph ⟦ d' ⟧ᵈ x) → (₁₊ n) ⊢ ⟦ d ⟧ᵈ ≈ ⟦ d' ⟧ᵈ)
  where

  ⟦_⟧ₖ : Kind PG n → Circuit n
  ⟦ lin y ⟧ₖ = [ ι y ]ʷ
  ⟦ tr e ⟧ₖ  = Xc e
  ⟦ phs g ⟧ₖ = ⟦ g ⟧ᵖ

  record NF (n : ℕ) : Set where
    constructor ⟨_,_,_⟩
    field
      shift    : Vec F n
      linear   : Word (LGen n)
      diagonal : D n

  ⌜_⌝ : NF n → Circuit n
  ⌜ ⟨ b , L , d ⟩ ⌝ = Xc b • ⌊ L ⌋ • ⟦ d ⟧ᵈ

  nf₀ : NF n
  nf₀ = ⟨ 0ᵛ , ε , d₀ ⟩

  nf₀-ε : n ⊢ ⌜ nf₀ {n} ⌝ ≈ ε
  nf₀-ε {n} = trans (cong Xc-zero (trans left-unit d₀-ε)) left-unit
    where open Width n

  step : NF n → Kind PG n → NF n
  step ⟨ b , L , d ⟩ (lin y) = ⟨ b , L • [ y ]ʷ , d ⋆ˡ y ⟩
  step ⟨ b , L , d ⟩ (tr e)  = ⟨ zipWith _+_ b (e ⋆ˣ* L) , L , d ⋆ᵗ e ⟩
  step ⟨ b , L , d ⟩ (phs g) = ⟨ b , L , app d g ⟩

  step-sound : (N : NF n) (k : Kind PG n) → n ⊢ ⌜ N ⌝ • ⟦ k ⟧ₖ ≈ ⌜ step N k ⌝
  step-sound {n} ⟨ b , L , d ⟩ (lin y) = begin
    (Xc b • ⌊ L ⌋ • ⟦ d ⟧ᵈ) • [ ι y ]ʷ        ≈⟨ trans assoc (back _ (trans assoc (back _ (lin-tr d y)))) ⟩
    Xc b • ⌊ L ⌋ • [ ι y ]ʷ • ⟦ d ⋆ˡ y ⟧ᵈ     ≈⟨ back _ (sym assoc) ⟩
    Xc b • (⌊ L ⌋ • [ ι y ]ʷ) • ⟦ d ⋆ˡ y ⟧ᵈ   ∎
    where open Width n
  step-sound {n} ⟨ b , L , d ⟩ (tr e) = begin
    (Xc b • ⌊ L ⌋ • ⟦ d ⟧ᵈ) • Xc e                    ≈⟨ trans assoc (back _ (trans assoc (back _ (tr-tr d e)))) ⟩
    Xc b • ⌊ L ⌋ • Xc e • ⟦ d ⋆ᵗ e ⟧ᵈ                 ≈⟨ back _ (trans (sym assoc) (trans (front _ (X-push* L e)) assoc)) ⟩
    Xc b • Xc (e ⋆ˣ* L) • ⌊ L ⌋ • ⟦ d ⋆ᵗ e ⟧ᵈ         ≈⟨ trans (sym assoc) (front _ (Xc-add b (e ⋆ˣ* L))) ⟩
    Xc (zipWith _+_ b (e ⋆ˣ* L)) • ⌊ L ⌋ • ⟦ d ⋆ᵗ e ⟧ᵈ ∎
    where open Width n
  step-sound {n} ⟨ b , L , d ⟩ (phs g) =
    trans assoc (back _ (trans assoc (back _ (app-sound d g))))
    where open Width n

  ----------------------------------------------------------------------
  -- Equal operators, equal normal forms

  private
    -- The value at 0 is the translation.
    shift-0 : (N : NF n) → fn ⌜ N ⌝ 0ᵛ ≡ NF.shift N
    shift-0 ⟨ b , L , d ⟩ = begin
      fn (Xc b • ⌊ L ⌋ • ⟦ d ⟧ᵈ) 0ᵛ             ≡⟨ fn-• (Xc b) (⌊ L ⌋ • ⟦ d ⟧ᵈ) 0ᵛ ⟩
      fn (Xc b) (fn (⌊ L ⌋ • ⟦ d ⟧ᵈ) 0ᵛ)        ≡⟨ Eq.cong (fn (Xc b)) (fn-• ⌊ L ⌋ ⟦ d ⟧ᵈ 0ᵛ) ⟩
      fn (Xc b) (fn ⌊ L ⌋ (fn ⟦ d ⟧ᵈ 0ᵛ))       ≡⟨ Eq.cong (λ y → fn (Xc b) (fn ⌊ L ⌋ y)) (diag d 0ᵛ) ⟩
      fn (Xc b) (fn ⌊ L ⌋ 0ᵛ)                   ≡⟨ Eq.cong (fn (Xc b)) (lin-0 L) ⟩
      fn (Xc b) 0ᵛ                              ≡⟨ Xc-0 b ⟩
      b                                         ∎
      where open ≡-Reasoning

    -- The linear part and the phases, once the translation is cancelled.
    fn-lin : (L : Word (LGen n)) (d : D n) (x : Labels n) → fn (⌊ L ⌋ • ⟦ d ⟧ᵈ) x ≡ fn ⌊ L ⌋ x
    fn-lin L d x = Eq.trans (fn-• ⌊ L ⌋ ⟦ d ⟧ᵈ x) (Eq.cong (fn ⌊ L ⌋) (diag d x))

    ph-lin : (L : Word (LGen n)) (d : D n) (x : Labels n) → ph (⌊ L ⌋ • ⟦ d ⟧ᵈ) x ≡ ph ⟦ d ⟧ᵈ x
    ph-lin L d x = Eq.trans (ph-• ⌊ L ⌋ ⟦ d ⟧ᵈ x)
                     (Eq.trans (Eq.cong (ph ⟦ d ⟧ᵈ x +_) (lin-ph L (fn ⟦ d ⟧ᵈ x))) (FR.+-identityʳ _))

    same-lin : (L L' : Word (LGen n)) (d d' : D n) →
               ⟦ ⌊ L ⌋ • ⟦ d ⟧ᵈ ⟧ ≐ ⟦ ⌊ L' ⌋ • ⟦ d' ⟧ᵈ ⟧ → ⟦ ⌊ L ⌋ ⟧ ≐ ⟦ ⌊ L' ⌋ ⟧
    same-lin L L' d d' e x = Eq.cong₂ _,_
      (Eq.trans (Eq.sym (fn-lin L d x)) (Eq.trans (Eq.cong proj₁ (e x)) (fn-lin L' d' x)))
      (Eq.trans (lin-ph L x) (Eq.sym (lin-ph L' x)))

    same-ph : (L L' : Word (LGen n)) (d d' : D n) →
              ⟦ ⌊ L ⌋ • ⟦ d ⟧ᵈ ⟧ ≐ ⟦ ⌊ L' ⌋ • ⟦ d' ⟧ᵈ ⟧ → ∀ x → ph ⟦ d ⟧ᵈ x ≡ ph ⟦ d' ⟧ᵈ x
    same-ph L L' d d' e x =
      Eq.trans (Eq.sym (ph-lin L d x)) (Eq.trans (Eq.cong proj₂ (e x)) (ph-lin L' d' x))

    -- The translation cancelled.
    no-shift : (A B : NF n) → NF.shift A ≡ NF.shift B → ⟦ ⌜ A ⌝ ⟧ ≐ ⟦ ⌜ B ⌝ ⟧ →
               ⟦ ⌊ NF.linear A ⌋ • ⟦ NF.diagonal A ⟧ᵈ ⟧ ≐ ⟦ ⌊ NF.linear B ⌋ • ⟦ NF.diagonal B ⟧ᵈ ⟧
    no-shift ⟨ b , L , d ⟩ ⟨ .b , L' , d' ⟩ refl e = cancelˡ-⟦⟧ (Xc b) (⌊ L ⌋ • ⟦ d ⟧ᵈ) (⌊ L' ⌋ • ⟦ d' ⟧ᵈ) e

    finish : (A B : NF n) → NF.shift A ≡ NF.shift B →
             n ⊢ ⌊ NF.linear A ⌋ ≈ ⌊ NF.linear B ⌋ → n ⊢ ⟦ NF.diagonal A ⟧ᵈ ≈ ⟦ NF.diagonal B ⟧ᵈ →
             n ⊢ ⌜ A ⌝ ≈ ⌜ B ⌝
    finish {n} ⟨ b , L , d ⟩ ⟨ .b , L' , d' ⟩ refl eL ed = back _ (cong eL ed)
      where open Width n

    shifts : (A B : NF n) → ⟦ ⌜ A ⌝ ⟧ ≐ ⟦ ⌜ B ⌝ ⟧ → NF.shift A ≡ NF.shift B
    shifts A B e = Eq.trans (Eq.sym (shift-0 A)) (Eq.trans (Eq.cong proj₁ (e 0ᵛ)) (shift-0 B))

  nf-complete : Complete n → (A B : NF (₁₊ n)) → ⟦ ⌜ A ⌝ ⟧ ≐ ⟦ ⌜ B ⌝ ⟧ → (₁₊ n) ⊢ ⌜ A ⌝ ≈ ⌜ B ⌝
  nf-complete IH A@(⟨ b , L , d ⟩) B@(⟨ b' , L' , d' ⟩) e =
    finish A B eb (linear-complete IH L L' (same-lin L L' d d' e'))
                  (unique IH d d' (same-ph L L' d d' e'))
    where
    eb = shifts A B e
    e' = no-shift A B eb e

  nf-complete₀ : (A B : NF 0) → ⟦ ⌜ A ⌝ ⟧ ≐ ⟦ ⌜ B ⌝ ⟧ → 0 ⊢ ⌜ A ⌝ ≈ ⌜ B ⌝
  nf-complete₀ A@(⟨ [] , L , d ⟩) B@(⟨ [] , L' , d' ⟩) e =
    finish A B refl (Width.trans (lin-none L) (Width.sym (lin-none L')))
                    (unique₀ d d' (same-ph L L' d d' (no-shift A B refl e)))

  ----------------------------------------------------------------------
  -- Decomposing circuits, given how the generators split

  module Run
    (kind : ∀ {n} → Gen n → Kind PG n)
    (kind-sound : ∀ {n} (g : Gen n) → n ⊢ [ g ]ʷ ≈ ⟦ kind g ⟧ₖ)
    where

    run : NF n → Circuit n → NF n
    run N [ g ]ʷ  = step N (kind g)
    run N ε       = N
    run N (w • v) = run (run N w) v

    run-sound : (N : NF n) (w : Circuit n) → n ⊢ ⌜ N ⌝ • w ≈ ⌜ run N w ⌝
    run-sound {n} N [ g ]ʷ = Width.trans (Width.back n _ (kind-sound g)) (step-sound N (kind g))
    run-sound {n} N ε = Width.right-unit
    run-sound {n} N (w • v) = begin
      ⌜ N ⌝ • w • v                 ≈⟨ sym assoc ⟩
      (⌜ N ⌝ • w) • v               ≈⟨ front _ (run-sound N w) ⟩
      ⌜ run N w ⌝ • v               ≈⟨ run-sound (run N w) v ⟩
      ⌜ run (run N w) v ⌝           ∎
      where open Width n

    decompose : (w : Circuit n) → n ⊢ w ≈ ⌜ run nf₀ w ⌝
    decompose {n} w = begin
      w                       ≈⟨ sym left-unit ⟩
      ε • w                   ≈⟨ front _ (sym nf₀-ε) ⟩
      ⌜ nf₀ ⌝ • w             ≈⟨ run-sound nf₀ w ⟩
      ⌜ run nf₀ w ⌝           ∎
      where open Width n

    private
      via : ∀ {n} → (∀ (A B : NF n) → ⟦ ⌜ A ⌝ ⟧ ≐ ⟦ ⌜ B ⌝ ⟧ → n ⊢ ⌜ A ⌝ ≈ ⌜ B ⌝) → Complete n
      via {n} nfc {w} {v} e =
        trans (decompose w)
          (trans (nfc (run nf₀ w) (run nf₀ v)
                    (≐-trans (sound (sym (decompose w))) (≐-trans e (sound (decompose v)))))
                 (sym (decompose v)))
        where open Width n

    -- Circuits of the level with the same operator are equal.
    completeness : (n : ℕ) → Complete n
    completeness zero    = via nf-complete₀
    completeness (suc n) = via (nf-complete (completeness n))
