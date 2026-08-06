------------------------------------------------------------------------
-- Presentations of groups
--
-- Index of the main results of the library
--
-- This module collects, in one place, the library's central theorems:
-- the completeness-by-normalization principle, the presentation
-- theorems for products of presented groups, the concrete verified
-- presentations, their unique-normal-form witnesses, and the monoid
-- isomorphisms of the amalgamation case studies.  Every result is
-- re-stated with a full type signature and proved by reference to its
-- home module, so this file also serves as a reading guide: the banner
-- of each section names the file where the proof lives.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module MainTheorems where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Nat using (ℕ ; suc ; 2+)
import Data.Nat.Properties as NatP
open import Data.Nat.Primality using (Prime)
open import Function.Definitions using (Congruent ; Injective)
open import Level using (Level ; 0ℓ)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.PropositionalEquality as Eq

open import Notations using (₁₊)
open import Word.Base using (Word ; WRel ; _ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsMonoidPresentationOf_
        ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike)
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; CommRel ; ConjRelʷ ; EmptyRel ; TrivialRel ; _⊕_ ; _⊕^_)
import Normalization.NormalForm.Setoid as SNF
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Uniqueness.Propositional as NFU

import Presentation.Construct.Properties.DirectProduct as DirectProduct
import Presentation.Construct.Properties.NDirectProduct as NDirectProduct
import Presentation.Construct.Properties.SemiDirectProduct2 as SemiDirectProduct
import Presentation.Construct.Properties.Amalgamation as Amalgamation
import Presentation.Construct.Properties.Extension as Extension

import Examples.Groups.Trivial as Trivial
open import Examples.Groups.Cyclic.Normalization using (_Cn,_===_)
import Examples.Groups.Cyclic.Normalization as CycNF
import Examples.Groups.Cyclic.Semantics as CycSem
import Examples.Groups.Cyclic.Theorems as CycThm
open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
import Examples.Groups.Symmetric.Normalization as SymNF
import Examples.Groups.Symmetric.Loose.Semantics as SymLoose
import Examples.Groups.Symmetric.Tight.Semantics as SymTight
import Examples.Groups.Symmetric.Theorems as SymThm
import Examples.Groups.Pauli.Presentation as Pauli
import Examples.Construct.SemiDirectProduct.SnD as SnD
import Examples.Amalgamations.CliffordT1 as CliffordT1
import Examples.Amalgamations.CliffordT1BaseUNF as CliffordT1Base
import Examples.Amalgamations.QutritCliffordT1 as QutritCliffordT1
import Examples.Amalgamations.U33Di as U33Di

------------------------------------------------------------------------
-- Completeness by normalization
--
-- Home: Normalization.NormalForm.Setoid.  A normal form nf with a
-- section inv-nf whose representatives are separated by the semantics
-- (UniqueNormalForm) upgrades soundness of ⟦_⟧ to completeness.

completeness-by-normalization :
  ∀ {X : Set} (Γ : WRel X) (NFs : Setoid 0ℓ 0ℓ)
    {c d : Level} (Sem : Setoid c d) (⟦_⟧ : Word X → Setoid.Carrier Sem)
    {nf : SNF.NormalForm Γ NFs}
    (unf : SNF.UniqueNormalForm Γ NFs Sem ⟦_⟧ nf) →
    Congruent (PB._≈_ Γ) (Setoid._≈_ Sem) ⟦_⟧ →
    Injective (PB._≈_ Γ) (Setoid._≈_ Sem) ⟦_⟧
completeness-by-normalization Γ NFs Sem ⟦_⟧ = SNF.by-normalization Γ NFs Sem ⟦_⟧

-- Conversely, completeness plus an exact section (nf ∘ inv-nf ≗ id)
-- makes a normal form unique for ⟦_⟧.

unique-nf-by-completeness :
  ∀ {X : Set} (Γ : WRel X) (NFs : Setoid 0ℓ 0ℓ)
    {c d : Level} (Sem : Setoid c d) (⟦_⟧ : Word X → Setoid.Carrier Sem)
    (nf : SNF.NormalForm Γ NFs) →
    (∀ {u} → Setoid._≈_ NFs
       (SNF.NormalForm.nf nf (SNF.NormalForm.inv-nf nf u)) u) →
    Injective (PB._≈_ Γ) (Setoid._≈_ Sem) ⟦_⟧ →
    SNF.UniqueNormalForm Γ NFs Sem ⟦_⟧ nf
unique-nf-by-completeness Γ NFs Sem ⟦_⟧ nf = SNF.by-completeness Γ NFs Sem ⟦_⟧ nf

------------------------------------------------------------------------
-- A grouplike monoid presentation is a group presentation
--
-- Home: Presentation.Definitions.  Every presentation in this library
-- is a monoid presentation; a Grouplike witness (a left inverse for
-- every generator) upgrades a monoid presentation of G's underlying
-- monoid to a group presentation of G.

monoid-presentation⇒group-presentation :
  ∀ {X : Set} {_===_ : WRel X} {a ℓ : Level} {G : Group a ℓ} →
  _===_ IsMonoidPresentationOf (Group.monoid G) →
  Grouplike _===_ →
  _===_ IsPresentationOf G
monoid-presentation⇒group-presentation mp gl =
  monoidPresentation⇒presentation mp gl

------------------------------------------------------------------------
-- Presentations of products of presented groups
--
-- Each alias below re-exports a construction theorem together with its
-- premise telescope; `dpres` (resp. `presentation`) is the presentation
-- of the product group built on the semantic side.
--
--   Direct-Product-Presentation Γ Δ G₁ G₂ p₁ p₂
--     .dpres : (Γ ⋄ Δ ⋄ CommRel) IsPresentationOf dp        [dp = G₁ × G₂]
--     .LiftUNF nfp₁ nfp₂ unfp₁ unfp₂ .unfp' : the pair normal form is
--       unique for the product semantics (uniqueness lifts from the
--       factors)
--   Home: Presentation.Construct.Properties.DirectProduct
module Direct-Product-Presentation = DirectProduct.Presentation

--   N-fold-Direct-Product-Presentation Γ G p
--     .presentation : ∀ n → (Γ ⊕^ n) IsPresentationOf ⊗-group n
--   Home: Presentation.Construct.Properties.NDirectProduct
module N-fold-Direct-Product-Presentation = NDirectProduct.Presentation

--   Semidirect-Product-Presentation Γ Δ conj hyph hypn G₁ G₂ p₁ p₂
--     .dpres : (Γ ⋄ Δ ⋄ ConjRelʷ conj) IsPresentationOf G1⋊G2
--     .LiftUNF nfp₁ nfp₂ unfp₁ unfp₂ .unfp' : the pair normal form is
--       unique for the semi-direct product semantics
--   Home: Presentation.Construct.Properties.SemiDirectProduct2
module Semidirect-Product-Presentation = SemiDirectProduct.Presentation

--   Amalgamated-Product-Presentation P₁ P₂ ad G₀ G₁ G₂ p₀ p₁ p₂
--     .dpres : (P₁ * P₂ ⋆ f₁ ⋆ f₂) IsPresentationOf amalgamation
--     .UNF nfp₀ exact₀ sect-coset .unfp : the alternating normal form
--       is unique for the amalgamated-product semantics, given two
--       first-order exactness certificates (base normal form; coset
--       table on section words)
--   Home: Presentation.Construct.Properties.Amalgamation
module Amalgamated-Product-Presentation = Amalgamation.ANF.Presentation

--   Group-Extension-Presentation S R̄ conj corr GN GQ et pN pQ ⟦_⟧₀ …
--     .presentation-of-extension : ext IsPresentationOf G
--   Home: Presentation.Construct.Properties.Extension
module Group-Extension-Presentation = Extension.Presentation

------------------------------------------------------------------------
-- Concrete presentations: the trivial group
--
-- Home: Examples.Groups.Trivial (two presentations, one over the empty
-- alphabet with no axioms, one over any alphabet with the coarsest
-- relation).

trivial-presentation :
  EmptyRel {⊥} IsPresentationOf Trivial.P1.Presentation.gp
trivial-presentation = Trivial.P1.Presentation.presentation

trivial-presentation′ :
  (A : Set) → TrivialRel {A} IsPresentationOf Trivial.P2.Presentation.gp A
trivial-presentation′ A = Trivial.P2.Presentation.presentation A

------------------------------------------------------------------------
-- Concrete presentations: cyclic groups
--
-- Home: Examples.Groups.Cyclic.{Normalization,Semantics,Theorems}.
-- One generator T with T^(n+1) = ε presents ℤ/(n+1)ℤ.

cyclic-presentation :
  ∀ {n} → ((₁₊ n) Cn,_===_) IsPresentationOf (CycSem.Cn-group (₁₊ n))
cyclic-presentation = CycThm.presentation

-- Order 0 separates monoid presentations from group presentations.
-- The cyclic group of order 0 is ℤ by definition, and read as a group
-- presentation the trivial relation T^0 = ε (i.e. ε = ε) does present
-- ℤ.  But all presentations here are monoid presentations, and as a
-- monoid presentation it presents the free monoid on one generator:
-- (ℕ, +, 0).  Grouplikeness — the hypothesis of
-- monoid-presentation⇒group-presentation — is exactly what fails at
-- order 0: the generator has no left inverse.

cyclic-monoid-presentation :
  (0 Cn,_===_) IsMonoidPresentationOf NatP.+-0-monoid
cyclic-monoid-presentation = CycThm.monoid-presentation

cyclic-unique-nf :
  ∀ n → NFBase.UniqueNormalForm (n Cn,_===_) (CycNF.NF n)
          (Eq.setoid (CycSem.Cn n)) (CycSem.⟦_⟧ {n}) (CycNF.nfp' n)
cyclic-unique-nf = CycThm.unique-nf

------------------------------------------------------------------------
-- Concrete presentations: symmetric groups as circuits
--
-- Home: Examples.Groups.Symmetric.*.  The one-gate circuit presentation
-- (order, yang-baxter, plus the structural rules cong↑/comm₂ added by
-- Circuit.Base.Lift-Relation) presents the group of permutations of
-- Fin n, and the coset-tower normal form is unique for both the loose
-- endofunction semantics and the tight permutation semantics.

symmetric-presentation :
  ∀ n → (n VRel,_===_) IsPresentationOf (SymTight.Permutation′-group n)
symmetric-presentation n = SymThm.Tight.presentation n

symmetric-unique-nf :
  ∀ n → let open NFU (n VRel,_===_) (SymNF.NF n)
                     (Group.setoid (SymTight.Permutation′-group n))
                     (SymTight.⟦_⟧ {n})
        in UniqueNormalForm (SymNF.inv-nf {n})
symmetric-unique-nf n = SymThm.Tight.unique-nf n

symmetric-unique-nf-loose :
  ∀ n → NFBase.UniqueNormalForm (n VRel,_===_) (SymNF.NF n)
          (SymLoose.Endo-setoid n) (SymLoose.⟦_⟧ {n}) (SymNF.nfp'-t n)
symmetric-unique-nf-loose n = SymThm.Loose.unique-nf n

symmetric-soundness :
  ∀ n → Congruent (PB._≈_ (n VRel,_===_))
          (Setoid._≈_ (SymLoose.Endo-setoid n)) (SymLoose.⟦_⟧ {n})
symmetric-soundness n = SymThm.Loose.soundness n

symmetric-completeness :
  ∀ n → Injective (PB._≈_ (n VRel,_===_))
          (Setoid._≈_ (SymLoose.Endo-setoid n)) (SymLoose.⟦_⟧ {n})
symmetric-completeness n = SymThm.Loose.completeness n

------------------------------------------------------------------------
-- Concrete presentations: Pauli groups, compositionally
--
-- Home: Examples.Groups.Pauli.Presentation.  For an odd prime p, the
-- n-qupit Pauli quotient (ℤ/pℤ × ℤ/pℤ)ⁿ is presented by assembling the
-- cyclic presentation with the binary and n-fold direct-product
-- constructions; no fresh coset enumeration is needed.

pauli-presentation :
  ∀ (p-2 : ℕ) (p-prime : Prime (2+ p-2)) (n : ℕ) →
  (Pauli.Γ-H p-2 p-prime ⊕^ n) IsPresentationOf (Pauli.Pauli-group p-2 p-prime n)
pauli-presentation p-2 p-prime = Pauli.Pauli-presentation p-2 p-prime

------------------------------------------------------------------------
-- Concrete presentations: wreath products ℤ/Nℤ ≀ Sₙ
--
-- Home: Examples.Construct.SemiDirectProduct.SnD.  The n-fold cyclic
-- product with the circuit presentation of Sₙ acting by permuting
-- coordinates presents the wreath product (signed permutations /
-- generalized symmetric groups; the hyperoctahedral group at N = 2).

wreath-presentation :
  ∀ n m →
  ((((suc m) Cn,_===_) ⊕^ n) ⋄ (n VRel,_===_) ⋄ ConjRelʷ (SnD.conj {n}))
    IsPresentationOf (SnD.Wreath.wreath-group n m)
wreath-presentation n m = SnD.Wreath.presentation n m

------------------------------------------------------------------------
-- Amalgamation case studies: single-qubit Clifford+T
--
-- Home: Examples.Amalgamations.CliffordT1.  The Clifford+T gate-set
-- presentation over {T, H, S, ω} is monoid-isomorphic to the
-- amalgamated free product of its T- and H-extensions over their
-- common subgroup presentation XSω, with the amalgam's alternating
-- coset normal form.

clifford+T-qubit-isomorphism :
  MonoidMorphisms.IsMonoidIsomorphism
    (Monoid.rawMonoid (PP.•-ε-monoid CliffordT1.CliffordT1._===_))
    (Monoid.rawMonoid (PP.•-ε-monoid CliffordT1.CliffordT1.amalPres))
    (CliffordT1.CliffordT1.f ʷ)
clifford+T-qubit-isomorphism = CliffordT1.CliffordT1.CliffordT1-isomorphism

-- The tower's base normal form ⟨ω⟩ × ⟨S⟩ (carrier Fin 8 × Fin 4,
-- radices 8·4) is unique for the direct-product semantics ℤ/8ℤ × ℤ/4ℤ,
-- lifted from the two cyclic unique-normal-form witnesses.
-- Home: Examples.Amalgamations.CliffordT1BaseUNF.

clifford+T-base-unique-nf :
  SNF.UniqueNormalForm (CliffordT1.Sω.Pω ⊕ CliffordT1.Sω.PS)
    (Eq.setoid (CycNF.NF 8 × CycNF.NF 4))
    (Group.setoid CliffordT1Base.Z8×Z4)
    CliffordT1Base.⟦_⟧ CliffordT1.Sω.nfp'
clifford+T-base-unique-nf = CliffordT1Base.unfp'

------------------------------------------------------------------------
-- Amalgamation case studies: single-qutrit Clifford+T
--
-- Home: Examples.Amalgamations.QutritCliffordT1, via a four-level
-- tower of coset normal forms over the cyclic base ⟨ζ⟩, ζ⁹ = ε.

clifford+T-qutrit-isomorphism :
  MonoidMorphisms.IsMonoidIsomorphism
    (Monoid.rawMonoid (PP.•-ε-monoid QutritCliffordT1.CliffordT1-Simplified._===_))
    (Monoid.rawMonoid (PP.•-ε-monoid QutritCliffordT1.CliffordT1-Simplified.amalPres))
    (QutritCliffordT1.CliffordT1-Simplified.f ʷ)
clifford+T-qutrit-isomorphism =
  QutritCliffordT1.CliffordT1-Simplified.CliffordT1-isomorphism

------------------------------------------------------------------------
-- Amalgamation case studies: U₃(ℤ[½, i])
--
-- Home: Examples.Amalgamations.U33Di.  The Bian–Selinger generators
-- and relations for U₃(ℤ[½, i]) are monoid-isomorphic to a two-level
-- amalgamated free product.

U₃-presentation-isomorphism :
  MonoidMorphisms.IsMonoidIsomorphism
    (Monoid.rawMonoid
      (PP.•-ε-monoid (U33Di.TwoLevel-Simplified-Amal.Amal.myANF.mypres)))
    (Monoid.rawMonoid
      (PP.•-ε-monoid U33Di.TwoLevel-Simplified-Amal.Simplified._===_))
    (U33Di.TwoLevel-Simplified-Amal.Iso.g ʷ)
U₃-presentation-isomorphism = U33Di.TwoLevel-Simplified-Amal.Iso.U33Di-isomorphism
