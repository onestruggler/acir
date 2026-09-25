------------------------------------------------------------------------
-- Presentations of groups
--
-- Sequential composition of path-sums is unital, associative and a
-- congruence, up to ≋
--
-- Amy's QPL 2018 paper states no laws for the composite ξ′ ∘ ξ of
-- definition 2.6; that it composes operators, U_{ξ′∘ξ} = U_ξ′ U_ξ
-- (proposition 2.7), is what makes composition associative, unital
-- and well defined on operators.  Here these are theorems about ∘ᴾ,
-- up to ≋ (definition 2.3, equality of the operators): path-sums
-- modulo ≋ form a category with idPS as identity (∘ᴾ-identityˡ,
-- ∘ᴾ-identityʳ, ∘ᴾ-assoc) on which ∘ᴾ is well defined (∘ᴾ-congˡ,
-- ∘ᴾ-congʳ, and both at once ∘ᴾ-cong).
--
-- None of them holds as an equation of path-sums.  The two
-- bracketings of a triple composite have normalisations (k + k′) + k″
-- and k + (k′ + k″), and path variables likewise, which are equal only
-- propositionally, so ≡ between them is not even well typed; and
-- polynomials are functions, which --safe without function
-- extensionality does not identify from pointwise equality.
--
-- Each law is a statement about amplitudes, proved through proposition
-- 2.7 (PathSum.Compose.Properties).  The unit laws read prop-2-7ʳ at
-- the identity, whose single path reaches its input with phase 0
-- (amp-idPS-δ).  Associativity is the functoriality of the operator,
-- applyᴾ-∘, read through prop-2-7ᶜ.  In ∘ᴾ-congˡ the left factor
-- enters prop-2-7ʳ only through its amplitudes; in ∘ᴾ-congʳ the right
-- factor enters prop-2-7ᶜ only through its column, which the operator
-- of the left factor maps linearly (applyᴾ-scale, applyᴾ-cong).  The
-- rest is the normalisations, carried between the two sides by powers
-- of √2 (scale-+, scale-exp).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Compose.Laws (M₀ : ℕ) where

open import Data.Bool.Base using (if_then_else_)
open import Data.Integer.Base using (ℤ; 0ℤ)
open import Data.Nat.Base using () renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same-≗)
open import PathSum.Base using (PathSum; phase; idPS)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using
  (amp-≗ˣ; amp-Σδ; hits-same; prop-2-7ʳ; applyᴾ; applyᴾ-cong;
   applyᴾ-scale; applyᴾ-∘; prop-2-7ᶜ)
open import PathSum.Compose.Sum M₀ using
  (if-cong; zpow-≡; scale-+; scale-exp; scale-rot; scale-Σᴮ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ; Σᴮ-cong; zpow; rot; rot-map; rot-exp; rot-0; scale;
   scale-map)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; _≋_; ≋-trans; outBit-μ; eval-0ᴾ-val)
open import PathSum.Polynomial using (x[_]; eval)

private
  variable
    n k k′ k″ m m′ m″ j j′ l l′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The identity

-- idPS has a single path, which hits its input with phase 0: its
-- column at w is the basis column δ w.

amp-idPS-δ : (w z : Assign n) → amp (idPS {n}) w z ≐ δ w z
amp-idPS-δ {n} w z = at (λ ())
  where
  at : (y : Assign 0) →
       (if hits (idPS {n}) w y z
        then zpow (eval (phase (idPS {n})) w y) else 0ᴬ) ≐ δ w z
  at y = if-cong
    (trans (hits-same idPS w y z)
           (same-≗ {x = outBit idPS w y} {x′ = w} {z = z} {z′ = z}
                   (λ i → outBit-μ idPS w y i x[ i ] refl)
                   (λ _ → refl)))
    (zpow-≡ (eval-0ᴾ-val w y))

-- ξ ∘ idPS: prop-2-7ʳ sums over idPS's single path, which reaches the
-- input x itself with phase 0.

private
  after-id : (ξ : PathSum n k m) (x z : Assign n) (y : Assign 0) →
             rot (eval (phase (idPS {n})) x y) (amp ξ (outBit idPS x y) z) ≐
             amp ξ x z
  after-id {n = n} ξ x z y =
    rot-exp {eval (phase (idPS {n})) x y} {0ℤ}
            (amp ξ (outBit idPS x y) z) (eval-0ᴾ-val x y)
    ∙ rot-0 (amp ξ (outBit idPS x y) z)
    ∙ amp-≗ˣ ξ (λ i → outBit-μ idPS x y i x[ i ] refl) z

amp-∘-idPS : (ξ : PathSum n k m) (x z : Assign n) →
             amp (ξ ∘ᴾ idPS) x z ≐ amp ξ x z
amp-∘-idPS ξ x z = prop-2-7ʳ ξ idPS x z ∙ after-id ξ x z (λ ())

-- idPS ∘ ξ: prop-2-7ʳ reads idPS's column at the state each path of ξ
-- hits, which is the basis column there (amp-Σδ).

amp-idPS-∘ : (ξ : PathSum n k m) (x z : Assign n) →
             amp (idPS ∘ᴾ ξ) x z ≐ amp ξ x z
amp-idPS-∘ ξ x z =
  prop-2-7ʳ idPS ξ x z
  ∙ Σᴮ-cong (λ y → rot-map (eval (phase ξ) x y)
                           (amp-idPS-δ (outBit ξ x y) z))
  ∙ ≐-sym (amp-Σδ ξ x z)

-- The unit laws.  ξ ∘ idPS has ξ's indices on the nose (0 + k is k);
-- idPS ∘ ξ has k + 0.

∘ᴾ-identityʳ : (ξ : PathSum n k m) → (ξ ∘ᴾ idPS) ≋ ξ
∘ᴾ-identityʳ {k = k} ξ x z = scale-map k (amp-∘-idPS ξ x z)

∘ᴾ-identityˡ : (ξ : PathSum n k m) → (idPS ∘ᴾ ξ) ≋ ξ
∘ᴾ-identityˡ {k = k} ξ x z =
  scale-map k (amp-idPS-∘ ξ x z)
  ∙ scale-exp (amp ξ x z) (sym (ℕ.+-identityʳ k))


------------------------------------------------------------------------
-- Associativity

-- Both bracketings apply U_ξ″ to U_ξ′ applied to the column of ξ.

amp-assoc : (ξ″ : PathSum n k″ m″) (ξ′ : PathSum n k′ m′)
            (ξ : PathSum n k m) (x z : Assign n) →
            amp ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) x z ≐ amp (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ)) x z
amp-assoc ξ″ ξ′ ξ x z =
  prop-2-7ᶜ (ξ″ ∘ᴾ ξ′) ξ x z
  ∙ applyᴾ-∘ ξ″ ξ′ (amp ξ x) z
  ∙ applyᴾ-cong ξ″ {applyᴾ ξ′ (amp ξ x)} {amp (ξ′ ∘ᴾ ξ) x}
                (λ w → ≐-sym (prop-2-7ᶜ ξ′ ξ x w)) z
  ∙ ≐-sym (prop-2-7ᶜ ξ″ (ξ′ ∘ᴾ ξ) x z)

∘ᴾ-assoc : (ξ″ : PathSum n k″ m″) (ξ′ : PathSum n k′ m′)
           (ξ : PathSum n k m) →
           ((ξ″ ∘ᴾ ξ′) ∘ᴾ ξ) ≋ (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ))
∘ᴾ-assoc {k″ = k″} {k′ = k′} {k = k} ξ″ ξ′ ξ x z =
  scale-map ((k ℕ+ k′) ℕ+ k″) (amp-assoc ξ″ ξ′ ξ x z)
  ∙ scale-exp (amp (ξ″ ∘ᴾ (ξ′ ∘ᴾ ξ)) x z) (ℕ.+-assoc k k′ k″)


------------------------------------------------------------------------
-- Congruence

-- A power of √2 passes through a sum of rotated amplitudes.

private
  Σrot-scale : ∀ i (e : Assign m → ℤ) (a : Assign m → Amp) →
               scale i (Σᴮ (λ y → rot (e y) (a y))) ≐
               Σᴮ (λ y → rot (e y) (scale i (a y)))
  Σrot-scale i e a =
    scale-Σᴮ i (λ y → rot (e y) (a y))
    ∙ Σᴮ-cong (λ y → scale-rot i (e y) (a y))

-- On the left: ξ′ enters prop-2-7ʳ only through its amplitudes, so the
-- hypothesis applies under the sum once the powers of √2 are moved
-- inside it.

∘ᴾ-congˡ : (ξ′ : PathSum n k′ m′) (η′ : PathSum n j′ l′)
           (ξ : PathSum n k m) → ξ′ ≋ η′ → (ξ′ ∘ᴾ ξ) ≋ (η′ ∘ᴾ ξ)
∘ᴾ-congˡ {k′ = k′} {j′ = j′} {k = k} ξ′ η′ ξ eq x z =
  scale-map (k ℕ+ j′) (prop-2-7ʳ ξ′ ξ x z)
  ∙ ≐-sym (scale-+ k j′ (Σᴮ (λ y → rot (eval (phase ξ) x y)
                                        (amp ξ′ (outBit ξ x y) z))))
  ∙ scale-map k (Σrot-scale j′ (λ y → eval (phase ξ) x y)
                               (λ y → amp ξ′ (outBit ξ x y) z))
  ∙ scale-map k (Σᴮ-cong (λ y → rot-map (eval (phase ξ) x y)
                                        (eq (outBit ξ x y) z)))
  ∙ scale-map k (≐-sym (Σrot-scale k′ (λ y → eval (phase ξ) x y)
                                      (λ y → amp η′ (outBit ξ x y) z)))
  ∙ scale-+ k k′ (Σᴮ (λ y → rot (eval (phase ξ) x y)
                                 (amp η′ (outBit ξ x y) z)))
  ∙ scale-map (k ℕ+ k′) (≐-sym (prop-2-7ʳ η′ ξ x z))

-- On the right: ξ enters prop-2-7ᶜ only through its column, and powers
-- of √2 pass through the operator of ξ′.

∘ᴾ-congʳ : (ξ′ : PathSum n k′ m′) (ξ : PathSum n k m)
           (η : PathSum n j l) → ξ ≋ η → (ξ′ ∘ᴾ ξ) ≋ (ξ′ ∘ᴾ η)
∘ᴾ-congʳ {k′ = k′} {k = k} {j = j} ξ′ ξ η eq x z =
  scale-map (j ℕ+ k′) (prop-2-7ᶜ ξ′ ξ x z)
  ∙ scale-exp (applyᴾ ξ′ (amp ξ x) z) (ℕ.+-comm j k′)
  ∙ ≐-sym (scale-+ k′ j (applyᴾ ξ′ (amp ξ x) z))
  ∙ scale-map k′ (applyᴾ-scale ξ′ j (amp ξ x) z)
  ∙ scale-map k′ (applyᴾ-cong ξ′ {λ w → scale j (amp ξ x w)}
                                 {λ w → scale k (amp η x w)}
                                 (λ w → eq x w) z)
  ∙ scale-map k′ (≐-sym (applyᴾ-scale ξ′ k (amp η x) z))
  ∙ scale-+ k′ k (applyᴾ ξ′ (amp η x) z)
  ∙ scale-exp (applyᴾ ξ′ (amp η x) z) (ℕ.+-comm k′ k)
  ∙ scale-map (k ℕ+ k′) (≐-sym (prop-2-7ᶜ ξ′ η x z))

-- On both sides at once.

∘ᴾ-cong : (ξ′ : PathSum n k′ m′) (η′ : PathSum n j′ l′)
          (ξ : PathSum n k m) (η : PathSum n j l) →
          ξ′ ≋ η′ → ξ ≋ η → (ξ′ ∘ᴾ ξ) ≋ (η′ ∘ᴾ η)
∘ᴾ-cong ξ′ η′ ξ η eq′ eq =
  ≋-trans {ξ = ξ′ ∘ᴾ ξ} {ζ = η′ ∘ᴾ ξ} {χ = η′ ∘ᴾ η}
          (∘ᴾ-congˡ ξ′ η′ ξ eq′) (∘ᴾ-congʳ η′ ξ η eq)
