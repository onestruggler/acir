------------------------------------------------------------------------
-- Presentations of groups
--
-- Discharging SemCentralExt's generator data.
--
-- Qubit.SemCentralExt derives the scalar cocycle from a record
-- `GeneratorData` — the correction G that one gate carries against a
-- word, plus its congruence, its normalisation, and f-axiom.  This file
-- supplies that record, at every width, from the factor set that
-- Qubit.SemFE already builds in full:
--
--     generator-data : (n : ℕ) → SCE.GeneratorData n
--
-- so the qubit scalar layer's cocycle, group and extension have no
-- hypotheses left.
--
-- The two obstacles, and what answers them.
--
-- 1. The kernels differ.  SemFE measures the defect in ℤ/8 (the
--    exponent of ω); CocycleGen's kernel is the group of WORDS over the
--    cyclic alphabet.  `emb k = T ^ toℕ k` transports one to the other,
--    and the only facts needed of it are that it is normalised (which is
--    definitional, T ^ 0 being ε) and multiplicative — `emb-∙`, which is
--    ℤ/8 addition being ℕ addition modulo 8 together with T ^ 8 ≈ ε.
--
-- 2. Naming SemFE's factor set makes terms detonate.  SemCentralExt's
--    header measures it: reducing `T ^ toℕ (SemFE.f …)` to weak head
--    normal form forces the exponent, hence the section, the bijective
--    normal form and the whole of ScalarKernel; and conversion reduces
--    to whnf before comparing.  The fix is to keep the factor set a
--    module PARAMETER (`From-FactorSet`), so that every term mentioning
--    it is neutral and nothing can unfold, and to instantiate it exactly
--    once, at the end, where the result type mentions no cocycle.  This
--    is the same discipline SemCentralExt uses for its three generic
--    lemmas, for the same reason.
--
-- The mathematical content is `agree`: CocycleGen's f, extended from the
-- generator data by the cocycle identity, IS the given factor set at
-- every pair of words.  That is the missing lemma SemCentralExt's header
-- names, and it is a structural induction on the first argument —
--
--   ε        both sides normalise;
--   [ a ]ʷ   by definition of G;
--   u • u'   the third clause of CocycleGen's f is the cocycle identity
--            solved for f (u • u') v, and the factor set satisfies that
--            same identity, so the two agree by cancellation.
--
-- Nothing in the induction inspects the factor set: it uses only the
-- four laws.  f-axiom and G-cong then both come from its congruence, and
-- G-ε from its right normalisation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.SemGeneratorData where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat as Nat using (ℕ ; _%_ ; _/_)
open import Data.Nat.DivMod using (m%n<n ; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (*-comm)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Notations
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_ ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP

open import ForStdlib.Data.Fin.Mod using (ℤ)
open import ForStdlib.Algebra.Construct.Extension using (Extension)
import ForStdlib.Algebra.Construct.CentralExtension as CE
open CE using (Cocycle)
import ForStdlib.Algebra.Construct.FactorSetExtension as FSE
open FSE using (FactorSet)

-- Qubit case: fix the prime to 2.
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen ; Circuit)

import Examples.Groups.ProjectiveClifford.Qubit.Selinger.Figure8-Mod-Scalar
  p-2 p-prime as MS

import Examples.Groups.Cyclic.Syntactics as Cy
open Cy using (T ; _Cn,_===_ ; order)

-- The two halves being joined: the record to be filled, and the factor
-- set that fills it.
import Examples.Groups.Clifford.Qubit.SemCentralExt as SCE
import Examples.Groups.Clifford.Qubit.SemFE as FE

open SCE using (ΓK ; module CGn ; K ; Q ; φ ; GeneratorData)

private
  module KB = PB ΓK
  module PK = PP ΓK
  module KFE = AbelianGroup FE.K

------------------------------------------------------------------------
-- The scalar has order 8, as a word
--
-- The cyclic axiom is stated over _^'_ (left-associated); CocycleGen and
-- everything below use _^_, so the two are matched once here.

T^8 : KB._≈_ (T ^ 8) ε
T^8 = KB.trans (KB.sym (PK.^'=^ {8} {T})) (KB.axiom order)

------------------------------------------------------------------------
-- Reducing an exponent modulo 8

T^-% : ∀ k → KB._≈_ (T ^ k) (T ^ (k % 8))
T^-% k = begin
  T ^ k
    ≡⟨ Eq.cong (T ^_) (m≡m%n+[m/n]*n k 8) ⟩
  T ^ (k % 8 Nat.+ (k / 8) Nat.* 8)
    ≈⟨ ^-+ T (k % 8) ((k / 8) Nat.* 8) ⟩
  T ^ (k % 8) • T ^ ((k / 8) Nat.* 8)
    ≈⟨ (cright refl' (Eq.cong (T ^_) (*-comm (k / 8) 8))) ⟩
  T ^ (k % 8) • T ^ (8 Nat.* (k / 8))
    ≈⟨ (cright sym (^^ T 8 (k / 8))) ⟩
  T ^ (k % 8) • (T ^ 8) ^ (k / 8)
    ≈⟨ (cright ^-cong (T ^ 8) ε (k / 8) T^8) ⟩
  T ^ (k % 8) • ε ^ (k / 8)
    ≈⟨ (cright ε^k=ε (k / 8)) ⟩
  T ^ (k % 8) • ε
    ≈⟨ right-unit ⟩
  T ^ (k % 8) ∎
  where
  open PB ΓK
  open PP ΓK
  open SR word-setoid

------------------------------------------------------------------------
-- The transport ℤ/8 → words
--
-- k ↦ Tᵏ.  Normalisation is definitional; multiplicativity is the mod-8
-- reduction above.

emb : ℤ 8 → Word Cy.X
emb k = T ^ toℕ k

private
  -- ℤ/8 addition is ℕ addition modulo 8, on the nose.
  toℕ-∙ : (j k : ℤ 8) → toℕ (j KFE.∙ k) ≡ (toℕ j Nat.+ toℕ k) % 8
  toℕ-∙ j k = toℕ-fromℕ< (m%n<n (toℕ j Nat.+ toℕ k) 8)

emb-ε : KB._≈_ (emb KFE.ε) ε
emb-ε = KB.refl

emb-∙ : (j k : ℤ 8) → KB._≈_ (emb (j KFE.∙ k)) (emb j • emb k)
emb-∙ j k = begin
  T ^ toℕ (j KFE.∙ k)            ≡⟨ Eq.cong (T ^_) (toℕ-∙ j k) ⟩
  T ^ ((toℕ j Nat.+ toℕ k) % 8)  ≈⟨ sym (T^-% (toℕ j Nat.+ toℕ k)) ⟩
  T ^ (toℕ j Nat.+ toℕ k)        ≈⟨ ^-+ T (toℕ j) (toℕ k) ⟩
  T ^ toℕ j • T ^ toℕ k          ∎
  where
  open PB ΓK
  open PP ΓK
  open SR word-setoid

------------------------------------------------------------------------
-- From a factor set to the generator data
--
-- The factor set is a PARAMETER: every term below that mentions it is
-- neutral, so nothing unfolds and no conversion check has to reduce the
-- defect.  It is instantiated once, at the end.

module From-FactorSet (n : ℕ) (γ : FactorSet FE.K (FE.Q n) (FE.φ n)) where

  private
    module Γ = FactorSet γ
    open FSE.IsNormalisedCocycle Γ.isNormalisedCocycle
      using (f-cong ; f-εˡ ; f-εʳ ; cocycle)

    module Kw = AbelianGroup (K n)
    module Qw = Group (Q n)

    open SR Kw.setoid

  ----------------------------------------------------------------------
  -- G: the correction one gate carries against a word

  G : Gen n → Circuit n → Word Cy.X
  G a v = emb (Γ.f [ a ]ʷ v)

  -- CocycleGen's extension of G, which is what GeneratorData's f-axiom
  -- and SemCentralExt's cocycle are stated over.
  cf : Circuit n → Circuit n → Word Cy.X
  cf = CGn.f n (φ n) G

  ----------------------------------------------------------------------
  -- The agreement lemma
  --
  -- Induction on the first argument.  The ε and [ a ]ʷ cases are the
  -- factor set's left normalisation and the definition of G; the third
  -- is cancellation against the factor set's own cocycle identity, both
  -- sides of which are the same three-factor product.

  agree : (u v : Circuit n) → Kw._≈_ (cf u v) (emb (Γ.f u v))
  agree ε        v = Kw.sym (KB.trans (KB.refl' (Eq.cong emb (f-εˡ v))) emb-ε)
  agree [ a ]ʷ   v = Kw.refl
  agree (u • u') v = begin
    (A' Kw.⁻¹ Kw.∙ B') Kw.∙ C'
      ≈⟨ Kw.∙-cong (Kw.∙-cong (Kw.⁻¹-cong (agree u u')) (agree u' v))
                   (agree u (u' • v)) ⟩
    (A Kw.⁻¹ Kw.∙ B) Kw.∙ C
      ≈⟨ Kw.assoc _ _ _ ⟩
    A Kw.⁻¹ Kw.∙ (B Kw.∙ C)
      ≈⟨ Kw.∙-congˡ (Kw.sym split) ⟩
    A Kw.⁻¹ Kw.∙ (A Kw.∙ D)
      ≈⟨ Kw.sym (Kw.assoc _ _ _) ⟩
    (A Kw.⁻¹ Kw.∙ A) Kw.∙ D
      ≈⟨ Kw.∙-congʳ (Kw.inverseˡ A) ⟩
    Kw.ε Kw.∙ D
      ≈⟨ Kw.identityˡ D ⟩
    D ∎
    where
    A  = emb (Γ.f u u')
    B  = emb (Γ.f u' v)
    C  = emb (Γ.f u (u' • v))
    D  = emb (Γ.f (u • u') v)
    A' = cf u u'
    B' = cf u' v
    C' = cf u (u' • v)

    -- The factor set's cocycle identity, transported to words.
    split : Kw._≈_ (A Kw.∙ D) (B Kw.∙ C)
    split = begin
      A Kw.∙ D
        ≈⟨ Kw.sym (emb-∙ (Γ.f u u') (Γ.f (u • u') v)) ⟩
      emb (Γ.f u u' KFE.∙ Γ.f (u • u') v)
        ≈⟨ KB.refl' (Eq.cong emb (cocycle u u' v)) ⟩
      emb (Γ.f u' v KFE.∙ Γ.f u (u' • v))
        ≈⟨ emb-∙ (Γ.f u' v) (Γ.f u (u' • v)) ⟩
      B Kw.∙ C ∎

  ----------------------------------------------------------------------
  -- The three conditions

  -- G descends to the quotient: the factor set does, and emb is a
  -- function.
  G-cong : (a : Gen n) {v v' : Circuit n} →
           PB._≈_ (n MS.CRel,_===_) v v' → KB._≈_ (G a v) (G a v')
  G-cong a e = KB.refl' (Eq.cong emb (f-cong Qw.refl e))

  -- … and it is normalised, the factor set being normalised on the
  -- right and emb sending 0 to ε.
  G-ε : (a : Gen n) → KB._≈_ (G a ε) ε
  G-ε a = KB.trans (KB.refl' (Eq.cong emb (f-εʳ [ a ]ʷ))) emb-ε

  -- Each relator carries the same correction on either side: by `agree`
  -- this is the factor set's congruence in the first argument, and a
  -- relator is a proof of that congruence.
  f-axiom : {u u' : Circuit n} → (n MS.CRel,_===_) u u' → (v : Circuit n) →
            KB._≈_ (cf u v) (cf u' v)
  f-axiom {u} {u'} r v = begin
    cf u v          ≈⟨ agree u v ⟩
    emb (Γ.f u v)   ≈⟨ KB.refl' (Eq.cong emb (f-cong (PB.axiom r) Qw.refl)) ⟩
    emb (Γ.f u' v)  ≈⟨ Kw.sym (agree u' v) ⟩
    cf u' v ∎

  generator-data : GeneratorData n
  generator-data = record
    { G       = G
    ; G-cong  = G-cong
    ; G-ε     = G-ε
    ; f-axiom = f-axiom
    }

------------------------------------------------------------------------
-- The generator data, at every width
--
-- SemFE.γ is unconditional — its section is discharged there from the
-- bijective normal form of the mod-scalar rule set — so this is too.
-- The application is the only place the concrete factor set is named,
-- and its result type mentions no cocycle, so nothing has to reduce.

generator-data : (n : ℕ) → GeneratorData n
generator-data n = From-FactorSet.generator-data n (FE.γ n)

------------------------------------------------------------------------
-- What that closes
--
-- SemCentralExt's cocycle, its central extension and its total group,
-- with no hypothesis left.

γᶜ : (n : ℕ) → Cocycle (K n) (Q n)
γᶜ n = SCE.γᶜ n (generator-data n)

Central-group : (n : ℕ) → Group 0ℓ 0ℓ
Central-group n = SCE.Central-group n (generator-data n)

Central-extension : (n : ℕ) → Extension (AbelianGroup.group (K n)) (Q n)
Central-extension n = SCE.Central-extension n (generator-data n)
