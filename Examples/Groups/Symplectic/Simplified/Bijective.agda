------------------------------------------------------------------------
-- Presentations of groups
--
-- A bijective normal form for the simplified symplectic rule set.
--
-- Proposition 2.55 (Presentation.Construct.Properties.Extension) asks
-- each factor for a BijectiveNormalForm, i.e. a Bijection from the word
-- setoid to the normal forms.  The library has a NormalForm — a
-- RightInverse — for the symplectic rule set (Symplectic.Normalization,
-- via the coset tower), which supplies
--
--     nf, inv-nf, nf-cong, nf-injective, inv-nf ∘ nf ≗ id.
--
-- What a Bijection needs on top is surjectivity of nf, i.e. the other
-- round trip
--
--     nf ∘ inv-nf ≡ id.
--
-- That is not part of a RightInverse, but it follows from uniqueness:
-- inv-nf ∘ nf ≗ id sends [nf (inv-nf u)] and [u] to symplectically equal
-- words, soundness sends those to equal symplectic maps, and the section
-- is injective on normal forms (Normalization.Uniqueness.⟦[]⟧-injective).
--
-- The rule set wanted downstream is the SIMPLIFIED one, whose congruence
-- is the same relation on words as the original's — Simplified.Iso's
-- isomorphism is the identity on words, so it gives the implications in
-- both directions (⟦⟧-cong one way, injective the other).  The normal
-- form is therefore transported rather than rebuilt: same nf, same
-- inv-nf, congruences routed through the isomorphism.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Symplectic.Simplified.Bijective
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Empty using (⊥-elim)
open import Function.Bundles using (Bijection)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (setoid)
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base using (ε)
open import Word.Properties using (≡-dec)
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
open import Normalization.NormalForm.Propositional using (BijectiveNormalForm)
import Normalization.NormalForm.Setoid as SNF

import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic using
  ( Circuit ; Gen ; SympGate ; H-gate ; S-gate ; CZ-gate
  ; gate₀ ; gate₁ ; gate₂ ; _↥ )
open import Examples.Groups.Symplectic.Normalization.Boxes p-2 p-prime using (NF)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using () renaming ([_] to nf→word)
open import Examples.Groups.Symplectic.Normalization p-2 p-prime
  using (nfp'-sec ; nfp'-sec-agree)
open import Examples.Groups.Symplectic.Normalization.Uniqueness p-2 p-prime
  using (⟦[]⟧-injective)
open import Examples.Groups.Symplectic.Normalization.Faithful1 p-2 p-prime
  using (⟦⟧-sound)

import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as Sim
import Examples.Groups.Symplectic.Simplified.Lemmas    p-2 p-prime g* g-gen as SimL
open import Examples.Groups.Symplectic.Simplified.Iso  p-2 p-prime g* g-gen
  using (Theorem-Sym-iso-Sim')

open Syn.Symplectic            using () renaming (_QRel,_===_ to _QRel,_===₁_)
open Syn.Symplectic-GroupLike  using () renaming (grouplike to grouplike₁)
open Sim.Simplified-Relations  using () renaming (_QRel,_===_ to _QRel,_===₂_)
open SimL.Symplectic-Sim-GroupLike using () renaming (grouplike to grouplike₂)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The two rule sets prove the same equations
--
-- Theorem-Sym-iso-Sim' is an isomorphism whose underlying map on words
-- is the identity, so its congruence is ≈₂ ⇒ ≈₁ and its injectivity is
-- the converse.

private
  module Tr (m : ℕ) where
    module W₁ = Group-Lemmas (m QRel,_===₁_) (grouplike₁ {m})
    module W₂ = Group-Lemmas (m QRel,_===₂_) (grouplike₂ {m})
    open GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                        (Group.rawGroup W₁.•-ε-group)
    open IsGroupIsomorphism (Theorem-Sym-iso-Sim' {m}) public
      using (⟦⟧-cong ; injective)

  ≈₂⇒≈₁ : {w v : Circuit n} →
          PB._≈_ (n QRel,_===₂_) w v → PB._≈_ (n QRel,_===₁_) w v
  ≈₂⇒≈₁ {n} = Tr.⟦⟧-cong n

  ≈₁⇒≈₂ : {w v : Circuit n} →
          PB._≈_ (n QRel,_===₁_) w v → PB._≈_ (n QRel,_===₂_) w v
  ≈₁⇒≈₂ {n} = Tr.injective n

------------------------------------------------------------------------
-- The normal form of the original rule set, and its missing round trip

nfˢ : Circuit n → NF n
nfˢ {n} = SNF.NormalForm.nf (nfp'-sec n)

invˢ : NF n → Circuit n
invˢ {n} = SNF.NormalForm.inv-nf (nfp'-sec n)

-- nf ∘ inv-nf ≡ id, by uniqueness of the section.
nf∘inv : (u : NF n) → nfˢ (invˢ u) ≡ u
nf∘inv {n} u = ⟦[]⟧-injective n (⟦⟧-sound claim)
  where
  claim : PB._≈_ (n QRel,_===₁_) (nf→word (nfˢ (invˢ u))) (nf→word u)
  claim = PB.trans (PB.sym (nfp'-sec-agree n (nfˢ (invˢ u))))
            (PB.trans (SNF.NormalForm.inv-nf∘nf=id (nfp'-sec n) {invˢ u})
                      (nfp'-sec-agree n u))

------------------------------------------------------------------------
-- The bijective normal form, for either rule set

bijective₁ : (n : ℕ) → BijectiveNormalForm (n QRel,_===₁_) (NF n)
bijective₁ n = record
  { bijection = record
    { to        = nfˢ
    ; cong      = SNF.NormalForm.nf-cong (nfp'-sec n)
    ; bijective =
        SNF.NormalForm.nf-injective (nfp'-sec n)
      , λ u → invˢ u , λ {z} z≈ →
          Eq.trans (SNF.NormalForm.nf-cong (nfp'-sec n) z≈) (nf∘inv u)
    }
  }

-- NOTE for Proposition 2.55's `nf-ε` (invˢ (nfˢ ε) ≡ ε).  It does NOT
-- hold by computation at a variable width: the tower's section is stuck
-- on n, so the term does not reduce.  Nor does it hold at all for this
-- section — Simplified.NfEps refutes it at every positive width, one
-- level of the tower's inverse being a concatenation whatever its
-- arguments.  What CAN be done is to change the section at that one
-- point; bijective₂ε below does, and rep-ε is the resulting nf-ε.

-- The same maps, with both congruences routed through Simplified.Iso.
bijective₂ : (n : ℕ) → BijectiveNormalForm (n QRel,_===₂_) (NF n)
bijective₂ n = record
  { bijection = record
    { to        = nfˢ
    ; cong      = λ eq → SNF.NormalForm.nf-cong (nfp'-sec n) (≈₂⇒≈₁ eq)
    ; bijective =
        (λ eq → ≈₁⇒≈₂ (SNF.NormalForm.nf-injective (nfp'-sec n) eq))
      , λ u → invˢ u , λ {z} z≈ →
          Eq.trans (SNF.NormalForm.nf-cong (nfp'-sec n) (≈₂⇒≈₁ z≈)) (nf∘inv u)
    }
  }

------------------------------------------------------------------------
-- Decidable equality of normal forms
--
-- NF n is nested Fins, Vecs and sums with one exception: an A box
-- carries a proof that its pair is not (₀ , ₀), and two proofs of a
-- negation cannot be compared without function extensionality.  So the
-- structural route to a decision procedure stops at the A boxes.
--
-- The section goes round them.  [_] turns a normal form into a word over
-- Gen n — a finite gate set, so words are decidable — equal words have
-- equal denotations, and Uniqueness.⟦[]⟧-injective recovers the FULL
-- propositional equality of normal forms from equal denotations, proof
-- component included.  That is exactly what makes the ≢ harmless: it is
-- pinned by the rest of the box rather than compared.

-- The gate set: three constructors, none of them at arity 0.
gate-dec : ∀ {k} → DecidableEquality (SympGate k)
gate-dec H-gate  H-gate  = yes Eq.refl
gate-dec H-gate  S-gate  = no λ ()
gate-dec S-gate  H-gate  = no λ ()
gate-dec S-gate  S-gate  = yes Eq.refl
gate-dec CZ-gate CZ-gate = yes Eq.refl

-- Wire-indexed generators: a gate at the bottom of the circuit, or a
-- generator shifted up one wire.  (gate₀ is absurd — SympGate 0 is
-- empty — and the mixed cases differ in head constructor.)
gen-dec : ∀ {n} → DecidableEquality (Gen n)
gen-dec (gate₀ ()) _
gen-dec (gate₁ h)  (gate₀ ())
gen-dec (gate₁ h)  (gate₁ h') with gate-dec h h'
... | yes Eq.refl = yes Eq.refl
... | no  h≢      = no λ { Eq.refl → h≢ Eq.refl }
gen-dec (gate₁ h)  (gate₂ h') = no λ ()
gen-dec (gate₁ h)  (y ↥)      = no λ ()
gen-dec (gate₂ h)  (gate₀ ())
gen-dec (gate₂ h)  (gate₁ h') = no λ ()
gen-dec (gate₂ h)  (gate₂ h') with gate-dec h h'
... | yes Eq.refl = yes Eq.refl
... | no  h≢      = no λ { Eq.refl → h≢ Eq.refl }
gen-dec (gate₂ h)  (y ↥)      = no λ ()
gen-dec (x ↥)      (gate₀ ())
gen-dec (x ↥)      (gate₁ h)  = no λ ()
gen-dec (x ↥)      (gate₂ h)  = no λ ()
gen-dec (x ↥)      (y ↥)      with gen-dec x y
... | yes Eq.refl = yes Eq.refl
... | no  x≢      = no λ { Eq.refl → x≢ Eq.refl }

NF-dec : ∀ n → DecidableEquality (NF n)
NF-dec n u v with ≡-dec gen-dec (nf→word u) (nf→word v)
... | yes eq  = yes (⟦[]⟧-injective n (⟦⟧-sound (PB.refl' (n QRel,_===₁_) eq)))
... | no  eq≢ = no λ { Eq.refl → eq≢ Eq.refl }

------------------------------------------------------------------------
-- The section patched at the identity
--
-- Proposition 2.55 wants the identity coset's representative to be the
-- empty word, and the tower's section cannot oblige.  But the section is
-- not part of the Bijection's data: it is recovered from the SURJECTIVITY
-- field, whose obligation at a normal form u is
--
--     ∃ w. ∀ z. z ≈ w → nfˢ z ≡ u,
--
-- and any w with that property will do.  At u = nfˢ ε the empty word has
-- it — nfˢ z ≡ nfˢ ε is nf-cong — so the witness may simply be replaced
-- there, and NF-dec is what lets the definition see when it is there.
--
-- Nothing else changes: `to`, its congruence and injectivity are
-- bijective₂'s, so the two normal forms agree as maps and differ only in
-- which word they pick out of the identity coset.

-- The patch itself is generic — it uses nothing about this rule set —
-- so it is NormalForm.Setoid.ε-section, and all that happens here is
-- supplying the decision procedure.
bijective₂ε : (n : ℕ) → BijectiveNormalForm (n QRel,_===₂_) (NF n)
bijective₂ε n =
  SNF.ε-section (n QRel,_===₂_) (setoid (NF n)) (bijective₂ n) (NF-dec n)

-- Proposition 2.55's nf-ε, at every width: the identity coset's
-- representative is the empty word, on the nose.  The decision cannot
-- reduce at a variable width — nfˢ ε is stuck — but it does not have to:
-- what settles the branch is that the two arguments ARE equal.
rep-ε : ∀ {n} →
        SNF.BijectiveNormalForm.inv-nf (bijective₂ε n) (nfˢ {n} ε) ≡ ε
rep-ε {n} =
  SNF.ε-section-rep (n QRel,_===₂_) (setoid (NF n)) (bijective₂ n) (NF-dec n)
