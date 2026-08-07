------------------------------------------------------------------------
-- Presentations of groups
--
-- Faithfulness at a width, from a normal form at that width
--
-- This closes the loop of the width induction.  The chain
--
--   tower at width n  ⟹  Faithful n  ⟹  ↑-inj n  ⟹  srel-wd n
--                                                 ⟹  tower at 1+n
--
-- is well founded because the srel-wd used to build level 1+n needs
-- only Faithful at level n, strictly below.  Every arrow but the
-- first was already available:
--
--   ↑-inj n   ⟸ Faithful n   SemInj.Injectivity! (sem-↑-inj is proved)
--   srel-wd n ⟸ ↑-inj n      SrelWDSem.Full.srel-wd-all
--
-- This module supplies the first.  Given any normal form at width n
-- whose section agrees with Section's [_], the uniqueness theorem
-- (Uniqueness.⟦[]⟧-injective, itself postulate-free) upgrades
-- soundness to completeness, which IS Faithful n.
--
-- The section hypothesis is what the tower must be shown to satisfy.
-- It is not vacuous but it is small: the tower's section is built by
-- Reidemeister–Schreier as (f ʷ) (inv-nf u) • [ c ]ᶜ, and Section's
-- [_] is [ u ] ↑ • [ c ]ᵐˡ, so the two differ only by the word-lift
-- versus _↑ (Word.Properties.wconcatmap-[f]ʷ) — the same bridge that
-- Symmetric/Loose/Uniqueness crosses with its to↑.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.FaithfulFrom
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Presentation.Base as PB
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
import Normalization.NormalForm.Uniqueness.Propositional as NFU

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (_≈ˢ_ ; Sp-group ; module Interpretation)
open Interpretation using (⟦_⟧)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using (NF ; [_])
open import Examples.Groups.Symplectic.Normalization.Uniqueness
  p-2 p-prime using (⟦[]⟧-injective ; sound)
open import Examples.Groups.Symplectic.Normalization.SemInj p-2 p-prime
  using (Faithful)

open import Algebra.Bundles using (Group)


------------------------------------------------------------------------
-- Faithfulness from a normal form

-- The uniqueness witness for any section that agrees with [_].  Two
-- normal forms with equal denotations under that section have equal
-- denotations under [_], so ⟦[]⟧-injective separates them.

unique-of : ∀ n (sec : NF n → Circuit n) →
            (∀ u → PB._≈_ (n QRel,_===_) (sec u) [ u ]) →
            ∀ {u v} → ⟦ sec u ⟧ ≈ˢ ⟦ sec v ⟧ → u ≡ v
unique-of n sec agree {u} {v} eq = ⟦[]⟧-injective n claim
  where
  claim : ⟦ [ u ] ⟧ ≈ˢ ⟦ [ v ] ⟧
  claim q = Eq.trans (Eq.sym (sound (agree u) q))
              (Eq.trans (eq q) (sound (agree v) q))

-- Hence completeness at width n: a normal form whose section agrees
-- with [_] makes the semantics injective, which is Faithful n.

faithful-from : ∀ n (nfp : NFBase.NormalForm (n QRel,_===_) (NF n)) →
                (∀ u → PB._≈_ (n QRel,_===_)
                         (SNF.NormalForm.inv-nf nfp u) [ u ]) →
                Faithful n
faithful-from n nfp agree w v =
  NFU.by-normalization (n QRel,_===_) (NF n)
    (Group.setoid (Sp-group n)) (⟦_⟧ {n}) {nfp}
    (record { unique = unique-of n (SNF.NormalForm.inv-nf nfp) agree })
    sound

-- The same over an arbitrary carrier, which is the form the tower
-- needs: the tower's carrier is CosetNF.tower-carrier ⊤ n, the same
-- recursion as NF n but a distinct stuck term at a variable width, so
-- it reaches NF n through a map rather than by conversion.  φ need
-- only be injective; the tower's is the evident isomorphism.
faithful-from′ : ∀ n {B : Set}
                 (nfp : NFBase.NormalForm (n QRel,_===_) B)
                 (φ : B → NF n) →
                 (∀ {u v} → φ u ≡ φ v → u ≡ v) →
                 (∀ u → PB._≈_ (n QRel,_===_)
                          (SNF.NormalForm.inv-nf nfp u) [ φ u ]) →
                 Faithful n
faithful-from′ n {B} nfp φ φ-inj agree w v =
  NFU.by-normalization (n QRel,_===_) B
    (Group.setoid (Sp-group n)) (⟦_⟧ {n}) {nfp}
    (record { unique =
        λ {u} {v'} eq → φ-inj (⟦[]⟧-injective n (eq' eq)) })
    sound
  where
  open SNF.NormalForm nfp using () renaming (inv-nf to gg)
  eq' : ∀ {u v' : B} → ⟦ gg u ⟧ ≈ˢ ⟦ gg v' ⟧ →
        ⟦ [ φ u ] ⟧ ≈ˢ ⟦ [ φ v' ] ⟧
  eq' {u} {v'} eq q = Eq.trans (Eq.sym (sound (agree u) q))
                        (Eq.trans (eq q) (sound (agree v') q))
