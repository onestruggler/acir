------------------------------------------------------------------------
-- Presentations of groups
--
-- Decoded words, and the hyperplane step of Lemma 8.8
--
-- A decoded word on 4 + m wires is a product of gadgets of several
-- kinds, each carried to a pair of distinct basis states by the affine
-- decoding (`D`, over the gadgets of Stable.GadgetAll, one family per
-- kind).  The rules of the decoding's alphabet have at most five
-- indices, and an affine word τ moves any five basis states into the
-- hyperplane where the top bit is 0 (Affine.Canon).  There the decoded
-- word is λ⁰ of one a width down (`D-top`, from GadgetAll.d-top), and
-- conjugating by τ is a renaming of its states (`D-eqv`, from the
-- equivariance of the decoding).  So an equation between decoded words
-- on 5 + m wires holds as soon as the one their states are moved to by τ
-- holds on 4 + m (`hyper`: λ⁰ carries derivations, CalcW.transport⁰) —
-- the paper's proof of Lemma 8.8 from one width to the next.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
import Examples.Groups.Clifford+CS.Stable.Gadget as Gadget
import Examples.Groups.Clifford+CS.Stable.GadgetAll as GadgetAll

module Examples.Groups.Clifford+CS.Stable.Hyper
  (c4 : Complete 4) (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (K : Set) (G₄ : K → Circuit 4)
  (ind₄ : ∀ κ → Gadget.Indep₀ 0 c4 (f4 0) (f5 0) (tr 0) (G₄ κ))
  (f6 : ∀ κ → Gadget.TopTarget 0 c4 (f4 0) (f5 0) (tr 0) (G₄ κ))
  (ssym : ∀ κ m → Gadget.SwapSym (suc m) c4 (f4 (suc m)) (f5 (suc m)) (tr (suc m))
                   (GadgetAll.gad c4 f4 f5 tr (G₄ κ) (ind₄ κ) (f6 κ) (suc m)))
  where

open import Data.Bool using (Bool)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_YVRel,_===_ ; embed)
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits
import Examples.Groups.Clifford+CS.Affine.Widen as Widen
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW

module GA = GadgetAll c4 f4 f5 tr

------------------------------------------------------------------------
-- Decoded words

-- A letter: a kind of gadget and the two basis states it is carried to.
Lit : ℕ → Set
Lit m = K × Vec Bool (₄₊ m) × Vec Bool (₄₊ m)

d : (κ : K) (m : ℕ) → Vec Bool (₄₊ m) → Vec Bool (₄₊ m) → Circuit (₄₊ m)
d κ m = GA.Dec.d (G₄ κ) (ind₄ κ) (f6 κ) (ssym κ) m

D : ∀ m → List (Lit m) → Circuit (₄₊ m)
D m []                  = ε
D m ((κ , p , q) ∷ ℓ)   = d κ m p q • D m ℓ

-- Every letter's two states are distinct.
Ne : ∀ {m} → List (Lit m) → Set
Ne = All λ { (κ , p , q) → p ≢ q }

------------------------------------------------------------------------
-- One width up

module _ (m : ℕ) where
  private
    module A₁ = Theory (₄₊ m)
    module Al₁ = Alpha (₄₊ m)
    module C₁ = Circuits (suc m) c4
    module Wd = Widen m c4
    module CW = CalcW m (f4 m) (f5 m) (tr m)
    open Tools ((suc (₄₊ m)) YVRel,_===_)

    ≡→≈ : ∀ {a b : Circuit (suc (₄₊ m))} → a ≡ b → (suc (₄₊ m)) ⊢ᵧ a ≈ b
    ≡→≈ Eq.refl = refl

  -- The states moved by an affine word, and put below a new top wire.
  ren : Word A₁.Lt → List (Lit (suc m)) → List (Lit (suc m))
  ren τ = map λ { (κ , p , q) → κ , Al₁.amapʷ τ p , Al₁.amapʷ τ q }

  up : List (Lit m) → List (Lit (suc m))
  up = map λ { (κ , p , q) → κ , p Wd.⁺ , q Wd.⁺ }

  -- With the top bit 0, a decoded word is λ⁰ of the one a width down.
  D-top : ∀ (ℓ : List (Lit m)) → (suc (₄₊ m)) ⊢ᵧ D (suc m) (up ℓ) ≈ λ⁰ʷ (D m ℓ)
  D-top []                = refl
  D-top ((κ , p , q) ∷ ℓ) = cong (GA.d-top (G₄ κ) (ind₄ κ) (f6 κ) (ssym κ) m p q) (D-top ℓ)

  private
    cancel : ∀ (τ : Word A₁.Lt) → (suc (₄₊ m)) ⊢ᵧ C₁.⟪ A₁.rev τ ⟫ʷ • C₁.⟪ τ ⟫ʷ ≈ ε
    cancel τ = embed (C₁.⟪⟫-cong (A₁.rev-inv′ τ))

    cancel′ : ∀ (τ : Word A₁.Lt) → (suc (₄₊ m)) ⊢ᵧ C₁.⟪ τ ⟫ʷ • C₁.⟪ A₁.rev τ ⟫ʷ ≈ ε
    cancel′ τ = embed (C₁.⟪⟫-cong (A₁.rev-inv τ))

  -- Conjugating a decoded word by an affine word renames its states.
  D-eqv : ∀ (τ : Word A₁.Lt) (ℓ : List (Lit (suc m))) → Ne ℓ →
          (suc (₄₊ m)) ⊢ᵧ C₁.⟪ τ ⟫ʷ • D (suc m) ℓ • C₁.⟪ A₁.rev τ ⟫ʷ ≈ D (suc m) (ren τ ℓ)
  D-eqv τ [] [] = trans (back _ left-unit) (cancel′ τ)
  D-eqv τ ((κ , p , q) ∷ ℓ) (ne ∷ nes) = begin
    t • (d κ (suc m) p q • D (suc m) ℓ) • t′
      ≈⟨ back t (front t′ (back _ (sym (trans (front _ (cancel τ)) left-unit)))) ⟩
    t • (d κ (suc m) p q • ((t′ • t) • D (suc m) ℓ)) • t′
      ≈⟨ by-passoc (□ • (□ • ((□ • □) • □)) • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
    (t • d κ (suc m) p q • t′) • (t • D (suc m) ℓ • t′)
      ≈⟨ cong (GA.Dec.eqvʷ (G₄ κ) (ind₄ κ) (f6 κ) (ssym κ) (suc m) τ p q ne) (D-eqv τ ℓ nes) ⟩
    D (suc m) (ren τ ((κ , p , q) ∷ ℓ)) ∎
    where
    t  = C₁.⟪ τ ⟫ʷ
    t′ = C₁.⟪ A₁.rev τ ⟫ʷ

  private
    D-unconj : ∀ (τ : Word A₁.Lt) (ℓ : List (Lit (suc m))) → Ne ℓ →
             (suc (₄₊ m)) ⊢ᵧ D (suc m) ℓ ≈ C₁.⟪ A₁.rev τ ⟫ʷ • D (suc m) (ren τ ℓ) • C₁.⟪ τ ⟫ʷ
    D-unconj τ ℓ nes = begin
      D (suc m) ℓ
        ≈⟨ sym (trans (front _ (cancel τ)) (trans left-unit (trans (back _ (cancel τ)) right-unit))) ⟩
      (t′ • t) • D (suc m) ℓ • (t′ • t)
        ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      t′ • (t • D (suc m) ℓ • t′) • t
        ≈⟨ back t′ (front t (D-eqv τ ℓ nes)) ⟩
      t′ • D (suc m) (ren τ ℓ) • t ∎
      where
      t  = C₁.⟪ τ ⟫ʷ
      t′ = C₁.⟪ A₁.rev τ ⟫ʷ

  -- The hyperplane step.
  hyper : ∀ (τ : Word A₁.Lt) (ℓ₁ ℓ₂ : List (Lit (suc m))) (k₁ k₂ : List (Lit m)) →
          Ne ℓ₁ → Ne ℓ₂ → ren τ ℓ₁ ≡ up k₁ → ren τ ℓ₂ ≡ up k₂ →
          (₄₊ m) ⊢ᵧ D m k₁ ≈ D m k₂ → (suc (₄₊ m)) ⊢ᵧ D (suc m) ℓ₁ ≈ D (suc m) ℓ₂
  hyper τ ℓ₁ ℓ₂ k₁ k₂ n₁ n₂ e₁ e₂ e = begin
    D (suc m) ℓ₁                     ≈⟨ D-unconj τ ℓ₁ n₁ ⟩
    t′ • D (suc m) (ren τ ℓ₁) • t    ≈⟨ ≡→≈ (Eq.cong (λ x → t′ • D (suc m) x • t) e₁) ⟩
    t′ • D (suc m) (up k₁) • t       ≈⟨ back t′ (front t (D-top k₁)) ⟩
    t′ • λ⁰ʷ (D m k₁) • t            ≈⟨ back t′ (front t (CW.transport⁰ e)) ⟩
    t′ • λ⁰ʷ (D m k₂) • t            ≈⟨ back t′ (front t (sym (D-top k₂))) ⟩
    t′ • D (suc m) (up k₂) • t       ≈⟨ ≡→≈ (Eq.cong (λ x → t′ • D (suc m) x • t) (Eq.sym e₂)) ⟩
    t′ • D (suc m) (ren τ ℓ₂) • t    ≈⟨ sym (D-unconj τ ℓ₂ n₂) ⟩
    D (suc m) ℓ₂ ∎
    where
    t  = C₁.⟪ τ ⟫ʷ
    t′ = C₁.⟪ A₁.rev τ ⟫ʷ
