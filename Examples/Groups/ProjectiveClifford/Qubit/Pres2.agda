------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-qubit Clifford group mod scalars (p = 2), presented in the
-- STRUCTURAL model: _Clifford,_===_ presents VSp n.
--
--     1 ─→ Pauli n ─→ VSp n ─→ Sp(2n, 2) ─→ 1
--
-- The relation is the one Qubit.Cocycle builds — Proposition 2.55's
-- extension presentation of the Pauli rule set by the simplified
-- symplectic one, along conj and corr — and Qubit.Presentation already
-- proves it presents CMS n, the SYNTACTIC model (Clifford words modulo
-- their action on P4).  VSp n is the same group described structurally,
-- as pairs (S , φ) of a symplectic map and a ℤ/4 phase function
-- refining its twist.
--
-- So there is no new mathematics here: the two models are isomorphic by
-- the denotation ⟦_⟧ᵛ (Qubit.Iso2.CMS≅VSp), and a presentation composes
-- with an isomorphism.  The composite interpretation is ⟦ _ ⟧ᵛ ∘ ⟦_⟧ —
-- a word is read as a Clifford operator mod scalars, and that operator
-- as its (symplectic map, phase) pair.
--
-- Which model to state a presentation in matters downstream rather than
-- here.  CMS n is defined by a quotient, so its elements are words and
-- equality is "acts the same on P4"; VSp n is defined by data, so its
-- elements are finite objects and equality is pointwise equality of two
-- functions.  The scalar layer above (Clifford.Qubit.ExactExtension)
-- takes its quotient in VSp for that reason.
--
-- The hypotheses are inherited verbatim from Qubit.Presentation, which
-- still owes Proposition 2.55 two inputs — Sec-trivial and Conj-trivial,
-- both discharged at width 0 and open above it.  Transporting along an
-- isomorphism cannot retire them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Pres2 where

open import Algebra.Bundles using (Group)
open import Algebra.Bundles.Raw using (RawGroup)
import Algebra.Morphism.Construct.Composition as MC
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Transitive)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

-- The relation, taken from the module that builds it.
open import Examples.Groups.ProjectiveClifford.Qubit.Cocycle
  using (_Clifford,_===_)

-- The syntactic model, and the presentation theorem over it.
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup
  using (CMS-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Presentation
  using (Sec-trivial ; Conj-trivial)
  renaming (presentation to presentation-CMS)

-- The structural model, and the isomorphism between the two.
open import Examples.Groups.ProjectiveClifford.Qubit.VSp
  using (Cliff ; _≈ᵛ_ ; ⟦_⟧ᵛ ; VSp-group)
open import Examples.Groups.ProjectiveClifford.Qubit.Iso2
  using (CMS≅VSp ; ≈ᵛ-trans)

------------------------------------------------------------------------
-- Transport along CMS n ≅ VSp n
--
-- The presentation's isomorphism runs from the word group to CMS n, and
-- CMS≅VSp continues to VSp n, so the two compose in that order.

private
  module Build (n : ℕ) (sec : Sec-trivial n) (cnj : Conj-trivial n) where

    module P = _IsPresentationOf_ (presentation-CMS {n} sec cnj)

    -- The word group is the presentation's own, so the transported
    -- witness reuses its grouplike structure unchanged.
    open GroupMorphisms (Group.rawGroup P.GL.•-ε-group)
                        (Group.rawGroup (VSp-group n))
      using (IsGroupIsomorphism)

    -- Transitivity of _≈ᵛ_, phrased as the composition wants it.  Both
    -- components of _≈ᵛ_ are pointwise equations, so the three points
    -- have to be bound by hand: unification never recovers them from a
    -- proof's type.
    ≈ᵛ-transitive : Transitive (RawGroup._≈_ (Group.rawGroup (VSp-group n)))
    ≈ᵛ-transitive {X} {Y} {Z} = ≈ᵛ-trans X Y Z

    -- Every implicit is given: ≈ᵛ-transitive is checked before the
    -- morphism arguments could solve G₃, and the type of the result
    -- fixes only the composite, splitting which back apart would be
    -- higher-order.
    iso : IsGroupIsomorphism (⟦_⟧ᵛ ∘ P.⟦_⟧)
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup P.GL.•-ε-group}
                                {G₂ = Group.rawGroup (CMS-group n)}
                                {G₃ = Group.rawGroup (VSp-group n)}
                                (λ {X} {Y} {Z} → ≈ᵛ-transitive {X} {Y} {Z})
                                {f = P.⟦_⟧} {g = ⟦_⟧ᵛ}
                                P.iso (CMS≅VSp n)

    pres : (n Clifford,_===_) IsPresentationOf (VSp-group n)
    pres = record { gl = P.gl ; ⟦_⟧ = ⟦_⟧ᵛ ∘ P.⟦_⟧ ; iso = iso }

------------------------------------------------------------------------
-- The presentation theorem

-- The extension relation presents the structural model of the Clifford
-- group mod scalars, on the same two inputs as the syntactic version.
presentation : ∀ {n} → Sec-trivial n → Conj-trivial n →
               (n Clifford,_===_) IsPresentationOf (VSp-group n)
presentation {n} sec cnj = Build.pres n sec cnj

-- Width 0, unconditionally.  Both inputs hold by computation there: the
-- identity coset's representative is ε on the nose, and the Pauli
-- alphabet (⊤ ⊎ ⊤) ⊎^ 0 is empty.  They are proved here rather than
-- imported because the syntactic side keeps only the general statement.
private
  sec-trivial-0 : Sec-trivial 0
  sec-trivial-0 = PB.refl

  conj-trivial-0 : Conj-trivial 0
  conj-trivial-0 ()

presentation-0 : (0 Clifford,_===_) IsPresentationOf (VSp-group 0)
presentation-0 = presentation sec-trivial-0 conj-trivial-0
