------------------------------------------------------------------------
-- Presentations of groups
--
-- A BIJECTIVE normal form for an extension, from bijective normal forms
-- of its two factors:
--
--     BijectiveNormalForm S NFS   →   BijectiveNormalForm R̄ NFQ
--       →  BijectiveNormalForm (extension-presentation S R̄ conj corr)
--                              (NFS × NFQ).
--
-- Proposition 2.55 (Presentation.Construct.Properties.Extension) already
-- builds the normal form itself: its Reidemeister–Schreier engine sends
-- a word to (the N-part it accumulates, the coset it lands in), and
-- CosetNF.SingleLevel.Transfer.nfp' packages that as a NormalForm on
-- NFS × NFQ.  What a Bijection needs on top is the other round trip,
--
--     nf ∘ inv-nf ≡ id,
--
-- and that is CosetNF's Transfer.Unique, whose two premises are met
-- here: the base factor is exact because nfpS is a bijection, and the
-- coset table is exact on sections because nfpQ is (Extension.
-- sect-coset).  So the upgrade needs no new hypothesis at all — the
-- inputs below are exactly the ones dpres takes, minus real-Q, which
-- only ever served surjectivity of the interpretation.
--
-- Why it is worth having.  A BijectiveNormalForm is what Proposition
-- 2.55 asks of each FACTOR, so this is what lets extensions be stacked:
-- with it, a group presented as an extension can itself be the quotient
-- factor of the next extension up.  That is exactly the gap at the
-- qubit scalar layer, where Clifford.Qubit.Presentation still assumes a
-- bijective normal form for the Clifford group modulo scalars.
--
-- Note the direction of the dependency: this module sits in
-- Normalization but imports Presentation.Construct, because the coset
-- data it works with — hᶜ, secᶜ, the table — is defined there.  It is a
-- leaf, so nothing in Presentation depends on it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Normalization.Construction where

open import Algebra.Bundles using (Group)
open import Data.Product using (_×_ ; ∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.NormalForm.Setoid as SNF

open import ForStdlib.Algebra.Construct.Extension using (Extension)
import Presentation.Construct.Properties.Extension as Ext

------------------------------------------------------------------------
-- Transport along a translation
--
-- A bijective normal form only ever sees its rule set through the
-- congruence, so it moves along any translation φ : Word Y → Word X that
-- is a congruence-isomorphism: normalise by translating first.  Note
-- what each hypothesis buys — φ-cong the congruence, φ-inj injectivity,
-- φ-surj the surjectivity, which is where the WITNESS comes from (the
-- normal form's own section is a word over the wrong alphabet, and no
-- round-trip lemma for φ is needed to correct it).
--
-- Two rule sets presenting the same group by translations in both
-- directions — Presentation.Morphism's StarGroupIsomorphism — supply all
-- three, so a normal form proved for one is inherited by the other.

module _ {X Y : Set} (Γ₁ : WRel X) (Γ₂ : WRel Y)
  (φ      : Word Y → Word X)
  (φ-cong : ∀ {w v} → PB._≈_ Γ₂ w v → PB._≈_ Γ₁ (φ w) (φ v))
  (φ-inj  : ∀ {w v} → PB._≈_ Γ₁ (φ w) (φ v) → PB._≈_ Γ₂ w v)
  (φ-surj : ∀ a → ∃ λ w → PB._≈_ Γ₁ (φ w) a)
  {NF : Set}
  where

  transport : BijectiveNormalForm Γ₁ NF → BijectiveNormalForm Γ₂ NF
  transport nfp = record
    { bijection = record
      { to        = nf ∘ φ
      ; cong      = λ e → nf-cong (φ-cong e)
      ; bijective =
          (λ e → φ-inj (nf-injective e))
        , λ u → proj₁ (φ-surj (inv-nf u)) , λ {z} z≈ →
            Eq.trans
              (nf-cong (PB._≈_.trans (φ-cong z≈) (proj₂ (φ-surj (inv-nf u)))))
              (nf∘inv u)
      }
    }
    where
    open SNF.BijectiveNormalForm nfp

    nf∘inv : ∀ u → nf (inv-nf u) ≡ u
    nf∘inv u = proj₂ (surjective u) (PB._≈_.refl)

------------------------------------------------------------------------
-- The extension recipe: a normal subgroup presentation S, a quotient
-- presentation R̄, the conjugation action and the cocycle.

module _ {N X : Set}
  (S : WRel N) (R̄ : WRel X)
  (conj : X → N → Word N) (corr : ∀ {u v} → R̄ u v → Word N)
  where

  -- The relation the recipe generates, and its raw mixed axioms.
  ext : WRel (N ⊎ X)
  ext = Ext.ext S R̄ conj corr

  extp : WRel (N ⊎ X)
  extp = Ext.extp S R̄ conj corr

  module _
    (GN GQ : Group 0ℓ 0ℓ)
    (et : Extension GN GQ)
    (pN : S IsPresentationOf GN)
    (pQ : R̄ IsPresentationOf GQ)
    (⟦_⟧₀ : (N ⊎ X) → Group.Carrier (Extension.total et))
    {NFS NFQ : Set}
    (nfpS : BijectiveNormalForm S NFS)
    (nfpQ : BijectiveNormalForm R̄ NFQ)
    where

    open Ext.Presentation S R̄ conj corr GN GQ et pN pQ ⟦_⟧₀ nfpS nfpQ

    ------------------------------------------------------------------
    -- The extension's normal forms are pairs
    --
    -- nf reads a word as (N-part, coset) and inv-nf puts it back as
    -- (f ʷ) of the N-part followed by the coset's section.  Injectivity
    -- and the congruence come with the NormalForm; surjectivity is the
    -- exactness Transfer.Unique supplies, which is where the two
    -- factors' bijectivity is spent — the base's directly, the
    -- quotient's through sect-coset.

    bijective :
      (real : Realises)
      (sound-ax : ∀ {w v} → extp w v →
                  Group._≈_ (Extension.total et) ⟦ w ⟧ ⟦ v ⟧)
      (sec-triv : Sec-trivial)
      (conj-triv : Conj-trivial) →
      BijectiveNormalForm ext (NFS × NFQ)
    bijective real sound-ax sec-triv conj-triv = record
      { bijection = record
        { to        = NFP.nf
        ; cong      = NFP.nf-cong
        ; bijective =
            NFP.nf-injective
          , λ u → NFP.inv-nf u , λ {z} z≈ →
              Eq.trans (NFP.nf-cong z≈) (Exact.nf'∘gg=id u)
        }
      }
      where
      open Normal-Form real sound-ax sec-triv conj-triv

      module NFP = SNF.NormalForm nfp

      -- The two premises of Transfer.Unique, both discharged by the
      -- factors' round trips: nf∘invS for the base, sect-coset for the
      -- table.
      module Exact =
        CTT.Unique grouplike sect-coset
          (SNF.BijectiveNormalForm.normalForm nfpS) nf∘invS
