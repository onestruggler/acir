------------------------------------------------------------------------
-- Presentations of groups
--
-- Group-likeness of the two rule sets compared in Qubit.Selinger.Iso:
-- every generator has a left inverse.
--
--   * On the Figure-8 side this is immediate from C2, C3 and C5, with
--     cong↑ for shifted gates.
--   * On the extension side a Pauli generator inherits its inverse from
--     the Pauli presentation, and a gate generator inherits its inverse
--     from the simplified symplectic presentation, corrected by the Pauli
--     word that lifting that inverse's derivation accumulates.
--
-- That correction is the corr-witness construction of
-- Presentation.Construct.Properties.Extension, replayed here: the copy
-- there lives inside a Presentation module whose GN must be
-- Pauli-group n, and the Extension record we have is over +ₚ-group n.
--
-- Doing it this way needs no shift lemma: the symplectic group-likeness
-- already covers shifted gates g ↥, and corr-witness is uniform in the
-- derivation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.GroupLike where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ⁿ' ; _ʰ')

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ ; EmptyRel ; _⊕^_
        ; module LeftRightCongruence)
open import Presentation.Construct.Properties.Extension using (RelTwist ; tw)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot
  using (p-2 ; p-prime ; g* ; g-gen)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8-Mod-Scalar p-2 p-prime as MS
open MS using (_CRel,_===_ ; srel ; lemma-cong↑)

open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; _Clifford,_===_ ; conj ; corr)
open import Examples.Groups.Pauli.Presentation p-2 p-prime
  using (Γ-H ; Pauli-presentation)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations using (_QRel,_===_)
import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen as SimL

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The Figure-8 side
--
-- H² = ε (C2), S⁴ = ε (C3) and CZ² = ε (C5) give each gate a left
-- inverse; a shifted generator inherits its inverse through cong↑.

grouplike-MS : Grouplike (n CRel,_===_)
grouplike-MS (gate₁ H-gate)  = [ gate₁ H-gate ]ʷ , PB.axiom (srel MS.c2)
grouplike-MS (gate₂ CZ-gate) = [ gate₂ CZ-gate ]ʷ , PB.axiom (srel MS.c5)
grouplike-MS (gate₁ S-gate)  = S' • S' • S' , claim
  where
  S' = [ gate₁ S-gate ]ʷ
  -- (S·(S·S))·S has to be rebracketed into S ^ 4 = S·(S·(S·S)).
  claim : PB._≈_ (_ CRel,_===_) ((S' • S' • S') • S') ε
  claim = PB.trans PB.assoc
            (PB.trans (PB.cong PB.refl PB.assoc)
                      (PB.axiom (srel MS.c3)))
grouplike-MS (gg ↥) with grouplike-MS gg
... | inv , eq = inv ↑' , lemma-cong↑ (inv • [ gg ]ʷ) ε eq
  where open Symplectic using () renaming (_↑ to _↑')

------------------------------------------------------------------------
-- The extension side

module GL (n : ℕ) where

  private
    Sᴾ = Γ-H ⊕^ n
    R̄  = n QRel,_===_

    glS : Grouplike Sᴾ
    glS = _IsPresentationOf_.gl (Pauli-presentation n)

    glQ : Grouplike R̄
    glQ = SimL.Symplectic-Sim-GroupLike.grouplike

  open PB (n Clifford,_===_) using () renaming (_≈_ to _≈ₑ_)
  open PB R̄  using () renaming (_≈_ to _≈q_)
  open Group-Lemmas Sᴾ glS using () renaming (_⁻¹ to _⁻¹ₛ ; inverseˡ to inverseˡₛ)
  open LeftRightCongruence Sᴾ EmptyRel
         (ConjRelʷ (conj {n}) ∪ RelTwist R̄ (corr {n})) using (lefts)

  private
    conjs  = conj {n} ⁿ'
    conjss = conj {n} ʰ'

    -- Moving a gate letter rightward past a Pauli word emits its
    -- conjugate: the ConjRelʷ axiom, left summand of the mixed part.
    lemma-comm1 : ∀ x w → [ [ x ]ʷ ]ᵣ • [ w ]ₗ ≈ₑ [ conjs x w ]ₗ • [ [ x ]ʷ ]ᵣ
    lemma-comm1 x [ y ]ʷ =
      PB.axiom (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm y x)))
    lemma-comm1 x ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
    lemma-comm1 x (w • v) =
      PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (lemma-comm1 x w) PB.refl)
          (PB.trans PB.assoc
            (PB.trans (PB.cong PB.refl (lemma-comm1 x v)) (PB.sym PB.assoc))))

    lemma-comm : ∀ w v → [ v ]ᵣ • [ w ]ₗ ≈ₑ [ conjss v w ]ₗ • [ v ]ᵣ
    lemma-comm w [ x ]ʷ = lemma-comm1 x w
    lemma-comm w ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
    lemma-comm w (v • u) =
      PB.sym
        (PB.trans (PB.sym PB.assoc)
          (PB.trans (PB.cong (PB.sym (lemma-comm (conjss u w) v)) PB.refl)
            (PB.trans PB.assoc
              (PB.trans (PB.cong PB.refl (PB.sym (lemma-comm w u)))
                        (PB.sym PB.assoc)))))

    -- The Pauli correction carried by a symplectic derivation.
    corr-witness : ∀ {a b} → a ≈q b →
      ∃ λ (w : Word (PauliGen n)) → [ a ]ᵣ ≈ₑ [ w ]ₗ • [ b ]ᵣ
    corr-witness PB.refl = ε , PB.sym PB.left-unit
    corr-witness (PB.sym p) with corr-witness p
    ... | wp , pp = (wp ⁻¹ₛ) ,
      PB.trans (PB.sym PB.left-unit)
        (PB.trans (PB.cong (PB.sym (lefts inverseˡₛ)) PB.refl)
          (PB.trans PB.assoc (PB.cong PB.refl (PB.sym pp))))
    corr-witness (PB.trans p q) with corr-witness p | corr-witness q
    ... | wp , pp | wq , pq = (wp • wq) ,
      PB.trans pp (PB.trans (PB.cong PB.refl pq) (PB.sym PB.assoc))
    corr-witness (PB.cong {_} {b} {_} {_} p q) with corr-witness p | corr-witness q
    ... | wp , pp | wq , pq = (wp • conjss b wq) ,
      PB.trans (PB.cong pp pq)
        (PB.trans PB.assoc
          (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
            (PB.trans (PB.cong PB.refl (PB.cong (lemma-comm wq b) PB.refl))
              (PB.trans (PB.cong PB.refl PB.assoc) (PB.sym PB.assoc)))))
    corr-witness PB.assoc      = ε , PB.trans PB.assoc (PB.sym PB.left-unit)
    corr-witness PB.left-unit  = ε , PB.refl
    corr-witness PB.right-unit = ε , PB.trans PB.right-unit (PB.sym PB.left-unit)
    corr-witness (PB.axiom r̄)  =
      corr r̄ , PB.axiom (_⋄_⋄_.mid (_∪_.right (tw r̄)))

    corrOf : ∀ {a b} → a ≈q b → Word (PauliGen n)
    corrOf p = proj₁ (corr-witness p)

    corrOf-eq : ∀ {a b} (p : a ≈q b) → [ a ]ᵣ ≈ₑ [ corrOf p ]ₗ • [ b ]ᵣ
    corrOf-eq p = proj₂ (corr-witness p)

  grouplike-Cl : Grouplike (n Clifford,_===_)
  grouplike-Cl (inj₁ y) = [ proj₁ (glS y) ]ₗ , lefts (proj₂ (glS y))
  grouplike-Cl (inj₂ x) =
    [ corrOf (proj₂ (glQ x)) ⁻¹ₛ ]ₗ • [ proj₁ (glQ x) ]ᵣ ,
    PB.trans PB.assoc
      (PB.trans
        (PB.cong PB.refl
          (PB.trans (corrOf-eq (proj₂ (glQ x))) PB.right-unit))
        (lefts inverseˡₛ))
