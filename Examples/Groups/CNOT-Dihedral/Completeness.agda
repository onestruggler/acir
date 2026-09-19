------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the CNOT-dihedral relations (Amy, Chen and Ross,
-- Sections 5 and 6), assembled from its parts
--
-- The paper's argument: every circuit equals a normal form D · A, a
-- diagonal normal form followed by an affine one (Proposition 5.6,
-- existence), and distinct normal forms denote distinct operators
-- (Proposition 6.4, uniqueness); hence two circuits with the same
-- operator have the same normal form and are equal.
--
-- What is proved here outright: soundness (Soundness), one-qubit
-- completeness (OneQubit), the derivable rules of Figure 2 that the
-- existence proof rests on (Derived), the separation step of the
-- uniqueness proof — that D · A = D′ · A′ as operators forces A = A′
-- and then D = D′, since a diagonal operator fixes basis states and
-- an affine one carries no phase — and the assembly.  What is taken as
-- hypotheses is what the paper takes from elsewhere or proves by
-- reordering circuits at every width: Lafont's normal forms for affine
-- circuits (Lemmas 5.5 and 6.3), the normalisation of diagonal circuits
-- (Lemma 5.3, from Lemma 5.2), the decomposition of a circuit into a
-- diagonal and an affine part (Lemma 5.1), and the uniqueness of
-- diagonal normal forms (Lemma 6.2, the multilinear-polynomial
-- argument).  They are bundled as a record of normal-form data, whose
-- fields name the paper's lemmas.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Completeness where

open import Algebra.Bundles using (Monoid)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)
open import Normalization.StarPresentation using (module MonoidSem)
import Normalization.NormalForm.Uniqueness.Propositional as NFU

open import Examples.Groups.CNOT-Dihedral.Semantics
open import Examples.Groups.CNOT-Dihedral.Syntactics
open import Examples.Groups.CNOT-Dihedral.Interpretation
open import Examples.Groups.CNOT-Dihedral.Soundness using (axiom-soundᴱ ; sound)

import Examples.Groups.CNOT-Dihedral.OneQubit as OneQubit
import Examples.Groups.CNOT-Dihedral.Derived

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Normal-form data at width n

record NormalForms (n : ℕ) : Set₁ where
  field
    -- Diagonal and affine normal forms (Definitions 4.7 and 4.3), read
    -- as circuits.
    DNF ANF : Set
    ⟨_⟩ᴰ : DNF → Circuit n
    ⟨_⟩ᴬ : ANF → Circuit n

    -- A diagonal circuit fixes every basis state; an affine one carries
    -- no phase.
    diagonal : ∀ D x → proj₁ (⟦ ⟨ D ⟩ᴰ ⟧ x) ≡ x
    affine   : ∀ A x → proj₂ (⟦ ⟨ A ⟩ᴬ ⟧ x) ≡ 0₈

    -- Existence (Proposition 5.6): every circuit is equal to a normal
    -- form.  In the paper: Lemma 5.1 (a diagonal part followed by an
    -- affine one, from the rules of Figure 2), Lemma 5.3 (diagonal
    -- circuits normalise, from Lemma 5.2 and R₇, R₈, R₉) and Lemma 5.5
    -- (Lafont).
    normalise : Circuit n → DNF × ANF
    normalise-sound : ∀ w → n ⊢ ⟨ proj₁ (normalise w) ⟩ᴰ • ⟨ proj₂ (normalise w) ⟩ᴬ ≈ w

    -- Uniqueness of each part: Lemma 6.2 (diagonal, by the multilinear
    -- polynomial of the phase) and Lemma 6.3 (affine, Lafont).
    unique-D : ∀ D D′ → ⟦ ⟨ D ⟩ᴰ ⟧ ≐ ⟦ ⟨ D′ ⟩ᴰ ⟧ → D ≡ D′
    unique-A : ∀ A A′ → ⟦ ⟨ A ⟩ᴬ ⟧ ≐ ⟦ ⟨ A′ ⟩ᴬ ⟧ → A ≡ A′

------------------------------------------------------------------------
-- Uniqueness of normal forms (Proposition 6.4)
--
-- If D · A and D′ · A′ have the same operator then, on every input x,
-- the basis state reached is that reached by A, resp. A′ (D fixes x),
-- so A = A′; and the phase is that of D, resp. D′ (A adds none), so
-- D = D′.

module Uniqueness (NFs : NormalForms n) where
  open NormalForms NFs

  private
    -- The operator of D · A, on x: A's basis state, D's phase.
    apply : ∀ D A x → ⟦ ⟨ D ⟩ᴰ • ⟨ A ⟩ᴬ ⟧ x ≡ (proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x))
    apply D A x = begin
      ⟦ ⟨ D ⟩ᴰ • ⟨ A ⟩ᴬ ⟧ x
        ≡⟨ ⟦⟧-• ⟨ D ⟩ᴰ ⟨ A ⟩ᴬ x ⟩
      (⟦ ⟨ D ⟩ᴰ ⟧ ⊙ ⟦ ⟨ A ⟩ᴬ ⟧) x
        ≡⟨⟩
      proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ (proj₁ (⟦ ⟨ D ⟩ᴰ ⟧ x))) ,
        proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x) + proj₂ (⟦ ⟨ A ⟩ᴬ ⟧ (proj₁ (⟦ ⟨ D ⟩ᴰ ⟧ x)))
        ≡⟨ Eq.cong (λ y → proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ y) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x) + proj₂ (⟦ ⟨ A ⟩ᴬ ⟧ y))
                   (diagonal D x) ⟩
      proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x) + proj₂ (⟦ ⟨ A ⟩ᴬ ⟧ x)
        ≡⟨ Eq.cong (λ p → proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x) + p) (affine A x) ⟩
      proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x) + 0₈
        ≡⟨ Eq.cong (proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) ,_) (+-identityʳ _) ⟩
      proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x) ∎
      where open Eq.≡-Reasoning

    -- Both parts of an operator are pairs of a basis state and a phase.
    pair-ext : ∀ {a b : Bits n} {p q : ℤ₈} → proj₁ {B = λ _ → ℤ₈} (a , p) ≡ proj₁ (b , q) →
               proj₂ {B = λ _ → ℤ₈} (a , p) ≡ proj₂ (b , q) → (a , p) ≡ (b , q)
    pair-ext Eq.refl Eq.refl = Eq.refl

  unique : ∀ D A D′ A′ → ⟦ ⟨ D ⟩ᴰ • ⟨ A ⟩ᴬ ⟧ ≐ ⟦ ⟨ D′ ⟩ᴰ • ⟨ A′ ⟩ᴬ ⟧ → D ≡ D′ × A ≡ A′
  unique D A D′ A′ e = unique-D D D′ same-D , unique-A A A′ same-A
    where
    -- On x, both readings agree componentwise.
    at : ∀ x → (proj₁ (⟦ ⟨ A ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D ⟩ᴰ ⟧ x))
             ≡ (proj₁ (⟦ ⟨ A′ ⟩ᴬ ⟧ x) , proj₂ (⟦ ⟨ D′ ⟩ᴰ ⟧ x))
    at x = Eq.trans (Eq.sym (apply D A x)) (Eq.trans (e x) (apply D′ A′ x))

    same-A : ⟦ ⟨ A ⟩ᴬ ⟧ ≐ ⟦ ⟨ A′ ⟩ᴬ ⟧
    same-A x = pair-ext (Eq.cong proj₁ (at x)) (Eq.trans (affine A x) (Eq.sym (affine A′ x)))

    same-D : ⟦ ⟨ D ⟩ᴰ ⟧ ≐ ⟦ ⟨ D′ ⟩ᴰ ⟧
    same-D x = pair-ext (Eq.trans (diagonal D x) (Eq.sym (diagonal D′ x))) (Eq.cong proj₂ (at x))

------------------------------------------------------------------------
-- Completeness (Theorem: the relations present the operators)

module Complete (NFs : NormalForms n) where
  open NormalForms NFs
  open Uniqueness NFs

  -- Two circuits with the same operator are equal.
  complete : ∀ {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → n ⊢ w ≈ v
  complete {w} {v} e =
    PB.trans (PB.sym (normalise-sound w))
      (PB.trans (same-nf (unique D A D′ A′ e′)) (normalise-sound v))
    where
    D  = proj₁ (normalise w)
    A  = proj₂ (normalise w)
    D′ = proj₁ (normalise v)
    A′ = proj₂ (normalise v)
    -- The normal forms have the same operator, by soundness.
    e′ : ⟦ ⟨ D ⟩ᴰ • ⟨ A ⟩ᴬ ⟧ ≐ ⟦ ⟨ D′ ⟩ᴰ • ⟨ A′ ⟩ᴬ ⟧
    e′ = ≐-trans (sound (normalise-sound w))
           (≐-trans e (≐-sym (sound (normalise-sound v))))
    same-nf : D ≡ D′ × A ≡ A′ → n ⊢ ⟨ D ⟩ᴰ • ⟨ A ⟩ᴬ ≈ ⟨ D′ ⟩ᴰ • ⟨ A′ ⟩ᴬ
    same-nf (eD , eA) = PB.refl' (n VRel,_===_) (Eq.cong₂ (λ d a → ⟨ d ⟩ᴰ • ⟨ a ⟩ᴬ) eD eA)

  -- With soundness: the relations present a sub-monoid of the
  -- operators on n wires.  The interpretation is the library's reading
  -- through the monoid, which is ⟦_⟧ (Interpretation.⟦⟧ᴱ-def).
  subpresentation : (n VRel,_===_) IsSubMonoidPresentationOf Op-monoid n
  subpresentation = record
    { ⟦_⟧  = MS.⟦_⟧
    ; mono = record
      { isMonoidHomomorphism = MS.Cong.isMonoidHomomorphism axiom-soundᴱ
      ; injective            = λ {w} {v} e → complete {w} {v} (≐-⟦⟧ᴱ {w = w} {v} e)
      }
    }
    where
    module MS = MonoidSem (n VRel,_===_) (Monoid.setoid (Op-monoid n))
                          (Op-monoid n) ⟦_⟧ᵍ

------------------------------------------------------------------------
-- One qubit, outright

one-qubit : ∀ {w v : Circuit 1} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 1 ⊢ w ≈ v
one-qubit = OneQubit.complete
