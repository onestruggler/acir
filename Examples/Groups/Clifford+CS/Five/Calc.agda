------------------------------------------------------------------------
-- Presentations of groups
--
-- The λ-calculus on words, control wire 4
--
-- λ⁰₄ is λ¹₄ between two X on wire 4, letter by letter.  From the joint
-- paper's items for generators — (F4) λ⁰(g) and λ¹(h) commute, (F5) g is
-- λ⁰(g) λ¹(g) — the same for words (`F4ʷ`, `F5ʷ`), and λ⁰ carries
-- four-wire derivations as λ¹ does (`transport⁰`).  Hence a word g on
-- the domain wires that commutes with a four-wire circuit G₄ on four
-- wires commutes with λ⁰(G₄) on five (`pass⁰`), and so does every
-- λ¹-image (`pass¹`): the gadget of the affine decoding is λ⁰(G₄).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Word.Base using (ε)
open import Examples.Groups.Clifford+CS.Syntactics using (Gen ; Circuit)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λᵈ ; λᵈ-sp)

module Examples.Groups.Clifford+CS.Five.Calc
  (F4ᵍ : ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ)
  (F5ᵍ : ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ)
  (x4x4 : ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics using (_↓ᵏ_ ; _⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.Transport using (λʷ ; AxOk ; transport)

------------------------------------------------------------------------
-- The readings

λ⁰ʷ dʷ : Circuit 4 → List Mac
λ⁰ʷ [ g ]ʷ  = X4 ∷ λ₁ g ∷ X4 ∷ []
λ⁰ʷ ε       = []
λ⁰ʷ (u • v) = λ⁰ʷ u ++ λ⁰ʷ v
dʷ [ g ]ʷ   = λᵈ g ∷ []
dʷ ε        = []
dʷ (u • v)  = dʷ u ++ dʷ v

Λ⁰ Λ¹ D : Circuit 4 → Circuit 5
Λ⁰ w = ⟪ λ⁰ʷ w ⟫ʷ
Λ¹ w = ⟪ λʷ w ⟫ʷ
D  w = ⟪ dʷ w ⟫ʷ

private
  ≡→≈ : ∀ {w v : Circuit 5} → w ≡ v → w ≈ v
  ≡→≈ Eq.refl = refl

X4w : Circuit 5
X4w = ⟪ X4 ∷ [] ⟫ʷ

hom⁰ : ∀ u v → Λ⁰ (u • v) ≈ Λ⁰ u • Λ⁰ v
hom⁰ u v = ⟪⟫-++ (λ⁰ʷ u) (λ⁰ʷ v)

hom¹ : ∀ u v → Λ¹ (u • v) ≈ Λ¹ u • Λ¹ v
hom¹ u v = ⟪⟫-++ (λʷ u) (λʷ v)

homᵈ : ∀ u v → D (u • v) ≈ D u • D v
homᵈ u v = ⟪⟫-++ (dʷ u) (dʷ v)

-- The domain reading is the circuit on the bottom four wires.
D-sp : ∀ w → D w ≈ w ↓ᵏ 1
D-sp [ g ]ʷ  = ≡→≈ (λᵈ-sp g)
D-sp ε       = refl
D-sp (u • v) = trans (homᵈ u v) (cong (D-sp u) (D-sp v))

------------------------------------------------------------------------
-- Commutation extends from letters to words

private
  -- If every A-letter commutes with every B-letter, every A-word commutes
  -- with every B-word.
  module Ext (A B : Circuit 4 → Circuit 5)
             (homA : ∀ u v → A (u • v) ≈ A u • A v) (εA : A ε ≈ ε)
             (homB : ∀ u v → B (u • v) ≈ B u • B v) (εB : B ε ≈ ε)
             (gens : ∀ g h → A [ g ]ʷ • B [ h ]ʷ ≈ B [ h ]ʷ • A [ g ]ʷ) where

    left : ∀ g v → A [ g ]ʷ • B v ≈ B v • A [ g ]ʷ
    left g [ h ]ʷ  = gens g h
    left g ε       = trans (back _ εB) (trans right-unit (trans (sym left-unit) (front _ (sym εB))))
    left g (u • v) = begin
      A [ g ]ʷ • B (u • v)              ≈⟨ back _ (homB u v) ⟩
      A [ g ]ʷ • (B u • B v)            ≈⟨ sym assoc ⟩
      (A [ g ]ʷ • B u) • B v            ≈⟨ front _ (left g u) ⟩
      (B u • A [ g ]ʷ) • B v            ≈⟨ assoc ⟩
      B u • (A [ g ]ʷ • B v)            ≈⟨ back _ (left g v) ⟩
      B u • (B v • A [ g ]ʷ)            ≈⟨ sym assoc ⟩
      (B u • B v) • A [ g ]ʷ            ≈⟨ front _ (sym (homB u v)) ⟩
      B (u • v) • A [ g ]ʷ              ∎

    words : ∀ u v → A u • B v ≈ B v • A u
    words [ g ]ʷ  v = left g v
    words ε       v = trans (front _ εA) (trans left-unit (trans (sym right-unit) (back _ (sym εA))))
    words (u • w) v = begin
      A (u • w) • B v                   ≈⟨ front _ (homA u w) ⟩
      (A u • A w) • B v                 ≈⟨ assoc ⟩
      A u • (A w • B v)                 ≈⟨ back _ (words w v) ⟩
      A u • (B v • A w)                 ≈⟨ sym assoc ⟩
      (A u • B v) • A w                 ≈⟨ front _ (words u v) ⟩
      (B v • A u) • A w                 ≈⟨ assoc ⟩
      B v • (A u • A w)                 ≈⟨ back _ (sym (homA u w)) ⟩
      B v • A (u • w)                   ∎

-- (F4) for words.
F4ʷ : ∀ u v → Λ⁰ u • Λ¹ v ≈ Λ¹ v • Λ⁰ u
F4ʷ = Ext.words Λ⁰ Λ¹ hom⁰ refl hom¹ refl gens
  where
  gens : ∀ g h → Λ⁰ [ g ]ʷ • Λ¹ [ h ]ʷ ≈ Λ¹ [ h ]ʷ • Λ⁰ [ g ]ʷ
  gens g h =
    trans (sym (⟪⟫-++ (λ⁰ʷ [ g ]ʷ) (λʷ [ h ]ʷ)))
      (trans (F4ᵍ g h) (⟪⟫-++ (λʷ [ h ]ʷ) (λ⁰ʷ [ g ]ʷ)))

-- (F5) for words.
F5ʷ : ∀ w → D w ≈ Λ⁰ w • Λ¹ w
F5ʷ [ g ]ʷ  = trans (F5ᵍ g) (⟪⟫-++ (λ⁰ʷ [ g ]ʷ) (λʷ [ g ]ʷ))
F5ʷ ε       = sym left-unit
F5ʷ (u • v) = begin
  D (u • v)                                 ≈⟨ homᵈ u v ⟩
  D u • D v                                 ≈⟨ cong (F5ʷ u) (F5ʷ v) ⟩
  (Λ⁰ u • Λ¹ u) • (Λ⁰ v • Λ¹ v)             ≈⟨ assoc ⟩
  Λ⁰ u • (Λ¹ u • (Λ⁰ v • Λ¹ v))             ≈⟨ back _ (sym assoc) ⟩
  Λ⁰ u • ((Λ¹ u • Λ⁰ v) • Λ¹ v)             ≈⟨ back _ (front _ (sym (F4ʷ v u))) ⟩
  Λ⁰ u • ((Λ⁰ v • Λ¹ u) • Λ¹ v)             ≈⟨ back _ assoc ⟩
  Λ⁰ u • (Λ⁰ v • (Λ¹ u • Λ¹ v))             ≈⟨ sym assoc ⟩
  (Λ⁰ u • Λ⁰ v) • (Λ¹ u • Λ¹ v)             ≈⟨ cong (sym (hom⁰ u v)) (sym (hom¹ u v)) ⟩
  Λ⁰ (u • v) • Λ¹ (u • v)                   ∎

------------------------------------------------------------------------
-- λ⁰ is λ¹ between two X on wire 4

Λ⁰-X : ∀ w → Λ⁰ w ≈ X4w • Λ¹ w • X4w
Λ⁰-X [ g ]ʷ  = refl
Λ⁰-X ε       = sym (trans (back _ left-unit) x4x4)
Λ⁰-X (u • v) = begin
  Λ⁰ (u • v)                                          ≈⟨ hom⁰ u v ⟩
  Λ⁰ u • Λ⁰ v                                         ≈⟨ cong (Λ⁰-X u) (Λ⁰-X v) ⟩
  (X4w • Λ¹ u • X4w) • (X4w • Λ¹ v • X4w)             ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  X4w • Λ¹ u • (X4w • X4w) • Λ¹ v • X4w               ≈⟨ back _ (back _ (front _ x4x4)) ⟩
  X4w • Λ¹ u • ε • Λ¹ v • X4w                         ≈⟨ back _ (back _ left-unit) ⟩
  X4w • Λ¹ u • Λ¹ v • X4w                             ≈⟨ back _ (sym assoc) ⟩
  X4w • (Λ¹ u • Λ¹ v) • X4w                           ≈⟨ back _ (front _ (sym (hom¹ u v))) ⟩
  X4w • Λ¹ (u • v) • X4w                              ∎

transport⁰ : AxOk → ∀ {u v} → 4 ⊢ u ≈ v → Λ⁰ u ≈ Λ⁰ v
transport⁰ ok {u} {v} e = trans (Λ⁰-X u) (trans (back _ (front _ (transport ok e))) (sym (Λ⁰-X v)))

------------------------------------------------------------------------
-- Passing λ⁰ of a four-wire circuit

-- A domain word commuting with G₄ on four wires passes λ⁰(G₄).
pass⁰ : AxOk → (g G₄ : Circuit 4) → 4 ⊢ g • G₄ ≈ G₄ • g →
        D g • Λ⁰ G₄ ≈ Λ⁰ G₄ • D g
pass⁰ ok g G₄ e = begin
  D g • Λ⁰ G₄                               ≈⟨ front _ (F5ʷ g) ⟩
  (Λ⁰ g • Λ¹ g) • Λ⁰ G₄                     ≈⟨ assoc ⟩
  Λ⁰ g • (Λ¹ g • Λ⁰ G₄)                     ≈⟨ back _ (sym (F4ʷ G₄ g)) ⟩
  Λ⁰ g • (Λ⁰ G₄ • Λ¹ g)                     ≈⟨ sym assoc ⟩
  (Λ⁰ g • Λ⁰ G₄) • Λ¹ g                     ≈⟨ front _ (sym (hom⁰ g G₄)) ⟩
  Λ⁰ (g • G₄) • Λ¹ g                        ≈⟨ front _ (transport⁰ ok e) ⟩
  Λ⁰ (G₄ • g) • Λ¹ g                        ≈⟨ front _ (hom⁰ G₄ g) ⟩
  (Λ⁰ G₄ • Λ⁰ g) • Λ¹ g                     ≈⟨ assoc ⟩
  Λ⁰ G₄ • (Λ⁰ g • Λ¹ g)                     ≈⟨ back _ (sym (F5ʷ g)) ⟩
  Λ⁰ G₄ • D g                               ∎

-- Every λ¹-image passes λ⁰(G₄).
pass¹ : (h G₄ : Circuit 4) → Λ¹ h • Λ⁰ G₄ ≈ Λ⁰ G₄ • Λ¹ h
pass¹ h G₄ = sym (F4ʷ G₄ h)
