------------------------------------------------------------------------
-- Presentations of groups
--
-- Definition 2.9 compositionally, for circuits over {H , S , CZ}
--
-- PathSum.Circuit interprets a Clifford circuit by running a state
-- through it, gate by gate: ⟦ C ⟧ is a single path-sum built in one
-- pass, not a composite of definition 2.6.  This module relates the
-- two readings of definition 2.9.
--
-- The gate set is made a GateModel (PathSum.Compose.Gates) with each
-- gate's path-sum the state machine's run on that gate alone,
-- cliffordGate g = ⟦ g ∷ [] ⟧, and its matrix PathSum.CircuitSemantics's
-- gateᴬ g; proposition 2.10 for one gate is prop-2-10 at g ∷ [].  The
-- compositional interpretation ⟦ C ⟧ᶜ, the gates' path-sums composed by
-- definition 2.6, then computes the circuit's matrix
-- (⟦⟧ᶜ-prop-2-10), and so it agrees with the state machine,
-- ⟦ C ⟧ᶜ ≋ ⟦ C ⟧ (⟦⟧ᶜ≋⟦⟧).  And the state machine satisfies the
-- paper's clause itself: ⟦ C₁ ++ C₂ ⟧ ≋ ⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧ (⟦++⟧).
--
-- Both are ≋, not ≡.  ⟦ C₁ ++ C₂ ⟧ has normalisation norm (C₁ ++ C₂)
-- where the composite has norm C₁ + norm C₂, equal only propositionally
-- (norm-++), so an equation between them is not even well typed;
-- polynomials are functions, which --safe does not identify from equal
-- values; and the path variables are in different orders -- the state
-- machine puts the newest Hadamard's variable first, definition 2.6
-- puts ξ′'s after ξ's.
--
-- Well-formedness of composites, which proposition 2.7 claims in
-- general and which fails in general (PathSum.Compose.Counterexample),
-- holds for circuits: the composite of two circuits is an isometry
-- (⟦∘⟧-Isometric, by PathSum.Compose.WellFormed's Isometric-∘ and
-- PathSum.Unitarity), and so WellFormed; and it is WellFormed also by
-- ⟦++⟧, since WellFormed is a property of the operator and
-- ⟦ C₁ ++ C₂ ⟧'s columns are unit vectors (⟦∘⟧-WellFormed).  The
-- compositional interpretation is an isometry as well (⟦⟧ᶜ-Isometric).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Compose.Clifford (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; _∧_)
open import Data.Integer.Base using (ℤ; _+_; _*_)
open import Data.Integer.Properties using (≤-reflexive)
open import Data.List.Base using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Adjoint M public using (norm-++)
open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using (PathSum)
open import PathSum.Circuit M using (Gate; H; S; CZ; Circuit; norm; ⟦_⟧)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; gateᴬ; applyᴬ; gateᴬ-cong; prop-2-10; ⟦⟧-unit-columns)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Gates M₀ using
  (GateModel; module Compositional; ≋-amp; Σrot-rot; Σrot-+)
open import PathSum.Compose.WellFormed M₀ using
  (WellFormed-≋; Isometric-∘)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; Σᴮ; rot)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_; ≋-sym)
open import PathSum.Isometry M₀ using (WellFormed)
open import PathSum.PartialIsometry M₀ using (Isometric; Isometric-≋)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Unitarity M₀ using (circuit-Isometric)

private
  variable
    n m : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The gate model

-- Each gate's path-sum is the state machine's run on it alone.  Its
-- normalisation and number of path variables are both norm (g ∷ []),
-- which holds by computation gate by gate, not for a variable g.

cliffordGate : (g : Gate n) → PathSum n (norm (g ∷ [])) (norm (g ∷ []))
cliffordGate (H w)    = ⟦ H w ∷ [] ⟧
cliffordGate (S w)    = ⟦ S w ∷ [] ⟧
cliffordGate (CZ w v) = ⟦ CZ w v ∷ [] ⟧

-- Proposition 2.10 for one gate.

cliffordGate-amp : (g : Gate n) (x z : Assign n) →
                   amp (cliffordGate g) x z ≐ gateᴬ g (δ x) z
cliffordGate-amp (H w)    = prop-2-10 (H w ∷ [])
cliffordGate-amp (S w)    = prop-2-10 (S w ∷ [])
cliffordGate-amp (CZ w v) = prop-2-10 (CZ w v ∷ [])

-- Each gate's matrix is built from entries of the column by rotations
-- and sums, so it is linear.

gateᴬ-lin : (g : Gate n) (e : Assign m → ℤ) (φ : Assign m → Column n)
            (z : Assign n) →
            gateᴬ g (λ w → Σᴮ (λ y → rot (e y) (φ y w))) z ≐
            Σᴮ (λ y → rot (e y) (gateᴬ g (φ y) z))
gateᴬ-lin (H w) e φ z i = trans
  (cong (Σᴮ (λ y → rot (e y) (φ y (z [ w ≔ false ]))) i +_)
        (Σrot-rot (½ * [ z w ]ᶻ) e (λ y → φ y (z [ w ≔ true ])) i))
  (Σrot-+ e (λ y → φ y (z [ w ≔ false ]))
            (λ y → rot (½ * [ z w ]ᶻ) (φ y (z [ w ≔ true ]))) i)
gateᴬ-lin (S w)    e φ z = Σrot-rot (¼ * [ z w ]ᶻ) e (λ y → φ y z)
gateᴬ-lin (CZ w v) e φ z = Σrot-rot (½ * [ z w ∧ z v ]ᶻ) e (λ y → φ y z)

cliffordGates : GateModel
cliffordGates = record
  { G         = Gate
  ; sizeᴳ     = λ g → norm (g ∷ [])
  ; gatePS    = cliffordGate
  ; gateᴳ     = gateᴬ
  ; gate-amp  = cliffordGate-amp
  ; gate-cong = gateᴬ-cong
  ; gate-lin  = gateᴬ-lin
  }

open Compositional cliffordGates public


------------------------------------------------------------------------
-- The compositional interpretation

-- Its normalisation and its matrix are the circuit's.

sizeᶜ≡norm : (C : Circuit n) → sizeᶜ C ≡ norm C
sizeᶜ≡norm []           = refl
sizeᶜ≡norm (H w ∷ C)    = cong suc (sizeᶜ≡norm C)
sizeᶜ≡norm (S w ∷ C)    = sizeᶜ≡norm C
sizeᶜ≡norm (CZ w v ∷ C) = sizeᶜ≡norm C

applyᴳ≡applyᴬ : (C : Circuit n) (ψ : Column n) → applyᴳ C ψ ≡ applyᴬ C ψ
applyᴳ≡applyᴬ []      ψ = refl
applyᴳ≡applyᴬ (g ∷ C) ψ = applyᴳ≡applyᴬ C (gateᴬ g ψ)

private
  -- Read at one entry.

  applyᴳ≐applyᴬ : (C : Circuit n) (ψ : Column n) (z : Assign n) →
                  applyᴳ C ψ z ≐ applyᴬ C ψ z
  applyᴳ≐applyᴬ C ψ z i = cong (λ φ → φ z i) (applyᴳ≡applyᴬ C ψ)

-- Proposition 2.10 for the compositional interpretation.

⟦⟧ᶜ-prop-2-10 : (C : Circuit n) (x z : Assign n) →
                amp ⟦ C ⟧ᶜ x z ≐ applyᴬ C (δ x) z
⟦⟧ᶜ-prop-2-10 C x z = prop-2-10ᶜ C x z ∙ applyᴳ≐applyᴬ C (δ x) z

-- The compositional interpretation agrees with the state machine.

⟦⟧ᶜ≋⟦⟧ : (C : Circuit n) → ⟦ C ⟧ᶜ ≋ ⟦ C ⟧
⟦⟧ᶜ≋⟦⟧ C = ≋-amp ⟦ C ⟧ᶜ ⟦ C ⟧ (sizeᶜ≡norm C)
  (λ x z → ⟦⟧ᶜ-prop-2-10 C x z ∙ ≐-sym (prop-2-10 C x z))


------------------------------------------------------------------------
-- ⟦ C₁ ; C₂ ⟧ = ⟦ C₂ ⟧ ∘ ⟦ C₁ ⟧ for the state machine

-- The state machine computes the circuit's matrix, so its composites
-- do too (simulate-∘).

amp-⟦++⟧ : (C₁ C₂ : Circuit n) (x z : Assign n) →
           amp ⟦ C₁ ++ C₂ ⟧ x z ≐ amp (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧) x z
amp-⟦++⟧ C₁ C₂ x z =
  prop-2-10 (C₁ ++ C₂) x z
  ∙ ≐-sym (applyᴳ≐applyᴬ (C₁ ++ C₂) (δ x) z)
  ∙ ≐-sym (simulate-∘ ⟦ C₁ ⟧ ⟦ C₂ ⟧ C₁ C₂ (machine C₁) (machine C₂) x z)
  where
  machine : (C : Circuit n) (x z : Assign n) →
            amp ⟦ C ⟧ x z ≐ applyᴳ C (δ x) z
  machine C x z = prop-2-10 C x z ∙ ≐-sym (applyᴳ≐applyᴬ C (δ x) z)

⟦++⟧ : (C₁ C₂ : Circuit n) → ⟦ C₁ ++ C₂ ⟧ ≋ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧)
⟦++⟧ C₁ C₂ = ≋-amp ⟦ C₁ ++ C₂ ⟧ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧) (norm-++ C₁ C₂)
                   (amp-⟦++⟧ C₁ C₂)


------------------------------------------------------------------------
-- Composites of circuits are well formed

-- The composite of two circuits is an isometry, each circuit being
-- one.

⟦∘⟧-Isometric : (C₁ C₂ : Circuit n) → Isometric (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧)
⟦∘⟧-Isometric C₁ C₂ =
  Isometric-∘ ⟦ C₂ ⟧ ⟦ C₁ ⟧ (circuit-Isometric C₂) (circuit-Isometric C₁)

-- And it is WellFormed, by ⟦++⟧: the columns of ⟦ C₁ ++ C₂ ⟧ are unit
-- vectors, and WellFormed is a property of the operator.

⟦∘⟧-WellFormed : (C₁ C₂ : Circuit n) → WellFormed (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧)
⟦∘⟧-WellFormed C₁ C₂ =
  WellFormed-≋ ⟦ C₁ ++ C₂ ⟧ (⟦ C₂ ⟧ ∘ᴾ ⟦ C₁ ⟧) (⟦++⟧ C₁ C₂)
    (λ x → ≤-reflexive (⟦⟧-unit-columns (C₁ ++ C₂) x))

-- The compositional interpretation is an isometry too.

⟦⟧ᶜ-Isometric : (C : Circuit n) → Isometric ⟦ C ⟧ᶜ
⟦⟧ᶜ-Isometric C = Isometric-≋ ⟦ C ⟧ ⟦ C ⟧ᶜ
  (≋-sym {ξ = ⟦ C ⟧ᶜ} {ζ = ⟦ C ⟧} (⟦⟧ᶜ≋⟦⟧ C)) (circuit-Isometric C)
