------------------------------------------------------------------------
-- Presentations of groups
--
-- Definition 2.9 read compositionally, for any gate set
--
-- Definition 2.9 of Amy's QPL 2018 paper interprets a circuit by
-- giving each gate a path-sum and composing:
--
--    ⟦ C₁ ; C₂ ⟧ = ⟦ C₂ ⟧ ∘ ⟦ C₁ ⟧ .
--
-- A GateModel is what that needs of a gate set: for every gate g on n
-- wires a path-sum gatePS g, with normalisation and path variables
-- both sizeᴳ g as definition 2.1 has it, and the gate's unnormalised
-- matrix gateᴳ g acting on columns (PathSum.CircuitSemantics's
-- Column), together with three facts.  gate-amp: the path-sum computes
-- the matrix on basis columns, proposition 2.10 for one gate.
-- gate-cong: the matrix respects equality of entries.  gate-lin: the
-- matrix is linear for the combinations that path-sums produce, sums
-- of columns rotated by powers of ζ.
--
-- Compositional then interprets a circuit, a list of gates, by the
-- paper's clause taken literally, first gate first:
--
--    ⟦ [] ⟧ᶜ = idPS          ⟦ g ∷ C ⟧ᶜ = ⟦ C ⟧ᶜ ∘ᴾ gatePS g ,
--
-- and proves proposition 2.10 for every circuit (prop-2-10ᶜ): the
-- amplitudes of ⟦ C ⟧ᶜ are the gates of C applied in turn to a basis
-- column.  The step is simulate-∘: if ξ computes the circuit C₁ and ξ′
-- computes C₂, then ξ′ ∘ᴾ ξ computes C₁ ++ C₂.  By proposition 2.7
-- (prop-2-7ʳ) the composite's column at x is Σ_y ζ^{P(x,y)} times ξ′'s
-- column at the state f(x,y) that the path y reaches, which is C₂
-- applied to that basis column; by gate-lin, C₂ may be applied after
-- the sum instead, and the sum is then ξ's column at x (amp-Σδ), which
-- is C₁ applied to |x⟩.  Only basis columns are ever fed to a gate's
-- path-sum, so gate-amp is all that is asked of it; that a gate's
-- path-sum acts as its matrix on every column is never needed.
--
-- Hence the paper's clause holds as a theorem about the interpretation
-- of a concatenation, ⟦ C₁ ++ C₂ ⟧ᶜ ≋ ⟦ C₂ ⟧ᶜ ∘ᴾ ⟦ C₁ ⟧ᶜ (⟦++⟧ᶜ), up to
-- ≋ and not as an equation: the two sides are bracketed differently
-- (C₁'s gates are composed onto ⟦ C₂ ⟧ᶜ one at a time on the left, all
-- at once on the right), and ∘ᴾ is associative only up to ≋
-- (PathSum.Compose.Laws).
--
-- The gates here act on all n wires, so the vertical compositions
-- that the paper leaves implicit never arise.  The instances are
-- PathSum.Compose.Clifford ({H, S, CZ}) and PathSum.Compose.CRK (the
-- paper's own {H, CNOT, R_k, R_k†}, with each gate's path-sum as the
-- paper prints it).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Gates (M₀ : ℕ) where

open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import Data.Nat.Properties as ℕ

open import PathSum.Base using (PathSum; phase; idPS)
open import PathSum.CircuitSemantics M₀ using (Column; δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Laws M₀ using (amp-idPS-δ)
open import PathSum.Compose.Properties M₀ using
  (hits-outBit; amp-Σδ; prop-2-7ʳ)
open import PathSum.Compose.Sum M₀ using
  (rot-comm; scale-exp; if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; _+ᴬ_; _≐_; Σᴮ; Σᴮ-cong; Σᴮ-+; rot; rot-map; rot-+ᴬ; rot-Σᴮ;
   scale-map)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Polynomial using (eval)

private
  variable
    n k k′ m m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Equivalence from amplitudes

-- Path-sums with the same normalisation and the same amplitudes are
-- equivalent.

≋-amp : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → k ≡ k′ →
        (∀ x z → amp ξ x z ≐ amp ζ x z) → ξ ≋ ζ
≋-amp {k′ = k′} ξ ζ k≡k′ eq x z =
  scale-map k′ (eq x z) ∙ scale-exp (amp ζ x z) (sym k≡k′)

-- Path-sums with the same path variables whose phases take the same
-- values, and whose outputs read the same bits, have the same
-- amplitudes -- whatever their coefficients.

amp-ext : (ξ : PathSum n k m) (ζ : PathSum n k′ m) →
          (∀ x y → eval (phase ξ) x y ≡ eval (phase ζ) x y) →
          (∀ x y w → outBit ξ x y w ≡ outBit ζ x y w) →
          ∀ x z → amp ξ x z ≐ amp ζ x z
amp-ext ξ ζ ph ob x z = Σᴮ-cong (λ y →
  if-cong (hits-outBit ξ ζ x x y y z (ob x y)) (zpow-≡ (ph x y)))


------------------------------------------------------------------------
-- Sums of rotated amplitudes

-- The combinations a gate has to be linear for, Σ_y ζ^{e(y)} a(y): a
-- rotation passes into them, and two of them with the same exponents
-- add term by term.

Σrot-rot : (c : ℤ) (e : Assign m → ℤ) (a : Assign m → Amp) →
           rot c (Σᴮ (λ y → rot (e y) (a y))) ≐
           Σᴮ (λ y → rot (e y) (rot c (a y)))
Σrot-rot c e a =
  rot-Σᴮ c (λ y → rot (e y) (a y)) ∙ Σᴮ-cong (λ y → rot-comm c (e y) (a y))

Σrot-+ : (e : Assign m → ℤ) (a b : Assign m → Amp) →
         (Σᴮ (λ y → rot (e y) (a y)) +ᴬ Σᴮ (λ y → rot (e y) (b y))) ≐
         Σᴮ (λ y → rot (e y) (a y +ᴬ b y))
Σrot-+ e a b =
  ≐-sym (Σᴮ-+ (λ y → rot (e y) (a y)) (λ y → rot (e y) (b y)))
  ∙ Σᴮ-cong (λ y → ≐-sym (rot-+ᴬ (e y) (a y) (b y)))


------------------------------------------------------------------------
-- Gate models

-- A gate set with, for each gate, its path-sum and its matrix.  The
-- field G is so named to keep clear of the gate types of the
-- instances.

record GateModel : Set₁ where
  field
    G         : ℕ → Set
    sizeᴳ     : ∀ {n} → G n → ℕ
    gatePS    : ∀ {n} (g : G n) → PathSum n (sizeᴳ g) (sizeᴳ g)
    gateᴳ     : ∀ {n} → G n → Column n → Column n

    -- Proposition 2.10 for one gate.
    gate-amp  : ∀ {n} (g : G n) (x z : Assign n) →
                amp (gatePS g) x z ≐ gateᴳ g (δ x) z

    gate-cong : ∀ {n} (g : G n) {φ φ′ : Column n} →
                (∀ z → φ z ≐ φ′ z) → ∀ z → gateᴳ g φ z ≐ gateᴳ g φ′ z

    gate-lin  : ∀ {n m} (g : G n) (e : Assign m → ℤ)
                (φ : Assign m → Column n) (z : Assign n) →
                gateᴳ g (λ w → Σᴮ (λ y → rot (e y) (φ y w))) z ≐
                Σᴮ (λ y → rot (e y) (gateᴳ g (φ y) z))


------------------------------------------------------------------------
-- Circuits over a gate model

module Compositional (𝔊 : GateModel) where

  open GateModel 𝔊

  -- The normalisation of a circuit, the sum of its gates'.

  sizeᶜ : List (G n) → ℕ
  sizeᶜ []      = 0
  sizeᶜ (g ∷ C) = sizeᴳ g ℕ+ sizeᶜ C

  -- Definition 2.9: ⟦ g ; C ⟧ = ⟦ C ⟧ ∘ ⟦ g ⟧.

  ⟦_⟧ᶜ : (C : List (G n)) → PathSum n (sizeᶜ C) (sizeᶜ C)
  ⟦ [] ⟧ᶜ    = idPS
  ⟦ g ∷ C ⟧ᶜ = ⟦ C ⟧ᶜ ∘ᴾ gatePS g

  -- The matrix of a circuit, gate by gate, first to last.

  applyᴳ : List (G n) → Column n → Column n
  applyᴳ []      ψ = ψ
  applyᴳ (g ∷ C) ψ = applyᴳ C (gateᴳ g ψ)

  -- U_(C₁;C₂) = U_C₂ U_C₁.

  applyᴳ-++ : (C₁ C₂ : List (G n)) (ψ : Column n) →
              applyᴳ (C₁ ++ C₂) ψ ≡ applyᴳ C₂ (applyᴳ C₁ ψ)
  applyᴳ-++ []       C₂ ψ = refl
  applyᴳ-++ (g ∷ C₁) C₂ ψ = applyᴳ-++ C₁ C₂ (gateᴳ g ψ)

  sizeᶜ-++ : (C₁ C₂ : List (G n)) →
             sizeᶜ (C₁ ++ C₂) ≡ sizeᶜ C₁ ℕ+ sizeᶜ C₂
  sizeᶜ-++ []       C₂ = refl
  sizeᶜ-++ (g ∷ C₁) C₂ = trans (cong (sizeᴳ g ℕ+_) (sizeᶜ-++ C₁ C₂))
                               (sym (ℕ.+-assoc (sizeᴳ g) (sizeᶜ C₁)
                                               (sizeᶜ C₂)))

  -- The matrix of a circuit respects equality of entries, and is
  -- linear for sums of rotated columns.

  applyᴳ-cong : (C : List (G n)) {φ φ′ : Column n} →
                (∀ z → φ z ≐ φ′ z) → ∀ z → applyᴳ C φ z ≐ applyᴳ C φ′ z
  applyᴳ-cong []      h = h
  applyᴳ-cong (g ∷ C) {φ} {φ′} h =
    applyᴳ-cong C {gateᴳ g φ} {gateᴳ g φ′} (gate-cong g h)

  applyᴳ-Σrot : (C : List (G n)) (e : Assign m → ℤ)
                (φ : Assign m → Column n) (z : Assign n) →
                applyᴳ C (λ w → Σᴮ (λ y → rot (e y) (φ y w))) z ≐
                Σᴮ (λ y → rot (e y) (applyᴳ C (φ y) z))
  applyᴳ-Σrot []      e φ z = λ _ → refl
  applyᴳ-Σrot (g ∷ C) e φ z =
    applyᴳ-cong C {gateᴳ g (λ w → Σᴮ (λ y → rot (e y) (φ y w)))}
                  {λ w → Σᴮ (λ y → rot (e y) (gateᴳ g (φ y) w))}
                  (gate-lin g e φ) z
    ∙ applyᴳ-Σrot C e (λ y → gateᴳ g (φ y)) z

  -- If ξ computes C₁ and ξ′ computes C₂ then ξ′ ∘ ξ computes C₁ ++ C₂.

  simulate-∘ : (ξ : PathSum n k m) (ξ′ : PathSum n k′ m′)
               (C₁ C₂ : List (G n)) →
               (∀ x z → amp ξ x z ≐ applyᴳ C₁ (δ x) z) →
               (∀ w z → amp ξ′ w z ≐ applyᴳ C₂ (δ w) z) →
               ∀ x z → amp (ξ′ ∘ᴾ ξ) x z ≐ applyᴳ (C₁ ++ C₂) (δ x) z
  simulate-∘ ξ ξ′ C₁ C₂ h₁ h₂ x z =
    prop-2-7ʳ ξ′ ξ x z
    ∙ Σᴮ-cong (λ y → rot-map (eval (phase ξ) x y) (h₂ (outBit ξ x y) z))
    ∙ ≐-sym (applyᴳ-Σrot C₂ (λ y → eval (phase ξ) x y)
                            (λ y → δ (outBit ξ x y)) z)
    ∙ applyᴳ-cong C₂ {λ w → Σᴮ (λ y → rot (eval (phase ξ) x y)
                                          (δ (outBit ξ x y) w))}
                     {applyᴳ C₁ (δ x)}
                     (λ w → ≐-sym (amp-Σδ ξ x w) ∙ h₁ x w) z
    ∙ (λ i → cong (λ ψ → ψ z i) (sym (applyᴳ-++ C₁ C₂ (δ x))))

  -- Proposition 2.10 for the compositional interpretation.

  prop-2-10ᶜ : (C : List (G n)) (x z : Assign n) →
               amp ⟦ C ⟧ᶜ x z ≐ applyᴳ C (δ x) z
  prop-2-10ᶜ []      x z = amp-idPS-δ x z
  prop-2-10ᶜ (g ∷ C) x z =
    simulate-∘ (gatePS g) ⟦ C ⟧ᶜ (g ∷ []) C (gate-amp g) (prop-2-10ᶜ C) x z

  -- ⟦ C₁ ; C₂ ⟧ = ⟦ C₂ ⟧ ∘ ⟦ C₁ ⟧, up to ≋.

  ⟦++⟧ᶜ : (C₁ C₂ : List (G n)) → ⟦ C₁ ++ C₂ ⟧ᶜ ≋ (⟦ C₂ ⟧ᶜ ∘ᴾ ⟦ C₁ ⟧ᶜ)
  ⟦++⟧ᶜ C₁ C₂ = ≋-amp ⟦ C₁ ++ C₂ ⟧ᶜ (⟦ C₂ ⟧ᶜ ∘ᴾ ⟦ C₁ ⟧ᶜ) (sizeᶜ-++ C₁ C₂)
    (λ x z → prop-2-10ᶜ (C₁ ++ C₂) x z
             ∙ ≐-sym (simulate-∘ ⟦ C₁ ⟧ᶜ ⟦ C₂ ⟧ᶜ C₁ C₂
                                 (prop-2-10ᶜ C₁) (prop-2-10ᶜ C₂) x z))
