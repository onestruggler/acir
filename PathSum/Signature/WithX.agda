------------------------------------------------------------------------
-- Presentations of groups
--
-- Preparing a wire in |1⟩ is preparing it in |0⟩ and applying X (Amy,
-- QPL 2018, definition 2.1)
--
-- The |0⟩-restrictions of PathSum.Ancilla, PathSum.Ancillas and
-- PathSum.Ancilla.Register prepare wires in |0⟩ only; an input
-- signature (PathSum.Signature) may also make a wire the constant 1.
-- For circuits over {H, X, CNOT, R_k, R_k†} (PathSum.CRK.WithX, which
-- contains the paper's gate set {H, CNOT, R_k} through its embed) the
-- two are related by the X gate, which maps the column |x⟩ to the
-- column with x's bit on its wire negated (amp-X, from proposition 2.10
-- for that gate set).
--
-- So a circuit X_w ; C with wire w prepared in |b⟩ is C with w prepared
-- in |1 ⊕ b⟩.  As path-sums with their constants inline -- the form in
-- which the paper writes a path-sum with constant inputs, a map from
-- the remaining variable inputs -- the two are equivalent
-- (X-prepares; at b = 0, preparing |1⟩ is preparing |0⟩ then X).  As
-- signed operators on all n qubits they differ by the relabelling of
-- their domains that X is: the column of the first at an input x with
-- x_w = b is the column of the second at x with x_w negated
-- (X-prepares-ampˢ).  The signed operators themselves are not equal --
-- one is defined on the inputs with x_w = b, the other on those with
-- x_w = 1 ⊕ b -- which is why the comparison is made on the inlined
-- path-sums, where the constant wire is no longer read
-- (PathSum.Signature.amp-inline-vars).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Signature.WithX (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; not; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (0ℤ)
open import Data.List.Base using (_∷_)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin

open import PathSum.Assign using
  (≔-here; ≔-there; same; same-true; same-intro)
open import PathSum.Compose.Properties M₀ using (amp-≗ˣ)
open import PathSum.Compose.Sum M₀ using (bool-iff)
open import PathSum.CRK.WithX M₀ using
  (X; Circuit; ⟦_⟧; norm; applyᴬ-cong; prop-2-10)
open import PathSum.Cyclotomic M₀ using (Amp; 0ᴬ; _≐_; zpow; scale-map)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.Hardness.Netlist using (flip; flip-cong; flip-flip)
open import PathSum.Signature M₀ using
  (pin; ampˢ; ampˢ-in; _⊢_; inline; amp-inline; at; Agrees-at; pin-at)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- X on columns

-- A basis column read at a flipped output is the column of the flipped
-- input.

private
  same-flip : (w : Fin n) (x z : Assign n) →
              same x (flip w z) ≡ same (flip w x) z
  same-flip w x z = bool-iff
    (λ h → same-intro (flip w x) z (λ i →
       trans (flip-cong w (same-true x (flip w z) h) i) (flip-flip w z i)))
    (λ h → same-intro x (flip w z) (λ i →
       trans (sym (flip-flip w x i))
             (flip-cong w (same-true (flip w x) z h) i)))

-- The column of X_w ; C at x is the column of C at x with x_w negated:
-- by proposition 2.10, X acts first, on the basis column |x⟩.

amp-X : (w : Fin n) (C : Circuit n) (x z : Assign n) →
        amp ⟦ X w ∷ C ⟧ x z ≐ amp ⟦ C ⟧ (flip w x) z
amp-X w C x z =
  prop-2-10 (X w ∷ C) x z
  ∙ applyᴬ-cong C (λ u i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
                               (same-flip w x u)) z
  ∙ ≐-sym (prop-2-10 C (flip w x) z)


------------------------------------------------------------------------
-- Preparing |b⟩, then X, is preparing |1 ⊕ b⟩

-- Writing b over x_w and then negating it is writing not b.

private
  flip-pin : (w : Fin n) (b : Bool) (x : Assign n) →
             ∀ i → flip w (pin (at w b) x) i ≡ pin (at w (not b)) x i
  flip-pin w b x i = go (i Fin.≟ w)
    where
    p : Assign _
    p = pin (at w b) x

    p-w : p w ≡ b
    p-w = trans (pin-at w b x w) (≔-here x w b)

    go : Dec (i ≡ w) → flip w p i ≡ pin (at w (not b)) x i
    go (yes refl) = trans (≔-here p w (not (p w)))
      (trans (cong not p-w)
             (sym (trans (pin-at w (not b) x w) (≔-here x w (not b)))))
    go (no i≢w)   = trans (≔-there p (not (p w)) i≢w)
      (trans (pin-at w b x i)
        (trans (≔-there x b i≢w)
               (sym (trans (pin-at w (not b) x i) (≔-there x (not b) i≢w)))))

-- With their constants inline, X_w ; C prepared in |b⟩ and C prepared
-- in |1 ⊕ b⟩ are equivalent path-sums; at b = 0, a wire prepared in |1⟩
-- is a wire prepared in |0⟩ followed by X.

X-prepares : (w : Fin n) (b : Bool) (C : Circuit n) →
             inline (at w b) ⟦ X w ∷ C ⟧ ≋ inline (at w (not b)) ⟦ C ⟧
X-prepares w b C x z = scale-map (norm C)
  (amp-inline (at w b) ⟦ X w ∷ C ⟧ x z
   ∙ amp-X w C (pin (at w b) x) z
   ∙ amp-≗ˣ ⟦ C ⟧ (flip-pin w b x) z
   ∙ ≐-sym (amp-inline (at w (not b)) ⟦ C ⟧ x z))

-- As signed operators: the column of X_w ; C prepared in |b⟩ at an
-- input with x_w = b is the column of C prepared in |1 ⊕ b⟩ at that
-- input with x_w negated.

X-prepares-ampˢ : (w : Fin n) (b : Bool) (C : Circuit n) (x z : Assign n) →
                  x w ≡ b →
                  ampˢ (at w b ⊢ ⟦ X w ∷ C ⟧) x z ≐
                  ampˢ (at w (not b) ⊢ ⟦ C ⟧) (flip w x) z
X-prepares-ampˢ w b C x z e =
  ampˢ-in (at w b ⊢ ⟦ X w ∷ C ⟧) (Equivalence.from (Agrees-at w b x) e) z
  ∙ amp-X w C x z
  ∙ ≐-sym (ampˢ-in (at w (not b) ⊢ ⟦ C ⟧)
             (Equivalence.from (Agrees-at w (not b) (flip w x))
               (trans (≔-here x w (not (x w))) (cong not e))) z)
