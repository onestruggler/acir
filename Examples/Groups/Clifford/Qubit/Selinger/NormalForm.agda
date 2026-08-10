------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger steps 3–4 (§4–5): the exact normal form for Clifford circuits.
--
-- The symplectic (phaseless) normal form N(n) — Selinger's Definitions
-- 4.3–4.4 and Lemma 5.5 — is already formalised in the symplectic layer:
--
--   * NF n              the normal-form data (Symplectic.Normalization.NF)
--   * nf→word : NF n → Word (Gen n)   the realising circuit; it satisfies
--       nf→word (nf , lm) = nf→word nf ↑ • [ lm ]ᵐˡ,
--     which is exactly Selinger's recursion N(n) = (N(n-1) ⊗ I)·M(n)·L(n)
--     with [ lm ]ᵐˡ = M(n)·L(n) built from the convenient gates A–E of
--     Figure 1;
--   * surjective : every symplectic map is realised by nf→word of some NF.
--
-- Selinger's *exact* normal form (Definition 4.5) is this word followed by
-- a global scalar ωᵖ, p ∈ {0,…,7}.  Under conjugation ω is invisible (it
-- is the ℤ/8 datum the ℤ/4 action `cact` cannot see — see Selinger.Action),
-- so it is exactly the extra parameter distinguishing the *exact* Clifford
-- group C(n) from its symplectic quotient Sp(2n,2).
--
-- The symplectic rules used here are the SIMPLIFIED ones, hence the
-- primitive-root parameters (g* , g-gen).  ω = (S·H)³ is not an axiom
-- there but the derived Simplified.Lemmas.Lemmas1.lemma-order-SH; its
-- soundness is obtained by transporting along Simplified.Iso, whose
-- underlying map on words is the identity, into Faithful1.⟦⟧-sound.
--
-- This file introduces the exact normal form and its realising circuit,
-- and proves Lemma 5.5 for everything below the scalar:
--
--   nf-existence      w ≈ nf→word (nfˢ w)            (existence)
--   nf-uniqueness     nf→word u ≈ nf→word v → u ≡ v  (uniqueness)
--   exact-existence   w ≈ ⟦ nfˢ w , p ⟧ᴺ, for ANY p
--   exact-uniqueness  ⟦ u , p ⟧ᴺ ≈ ⟦ v , q ⟧ᴺ → u ≡ v
--   scalar-invisible  ⟦ u , p ⟧ᴺ ≈ ⟦ u , q ⟧ᴺ
--   act-determines-nf  same action ⇒ same symplectic part
--
-- all with respect to the symplectic congruence, where ω ≈ ε (ω≈ε).  So
-- the symplectic layer pins the NF component down exactly and says
-- nothing whatever about the scalar: p is precisely the datum the
-- quotient forgets, and the ℤ/8 layer of Qubit.ExactExtension is
-- precisely what has to supply it.
--
-- WHAT IS MISSING for the exact statement (Figure 8 rather than the
-- symplectic rule set).  Qubit.ExactExtension.ExactData asks for
--
--   scalars    : w acts trivially on P4  ⇒  w ≈ᶠ ωᵏ for some k,
--   ω-faithful : ωʲ ≈ᶠ ωᵏ ⇒ j ≡ k.
--
-- The route to the first is "≈ mod scalars ⇒ ≈ up to ωᵏ", by induction
-- on the mod-scalar derivation; its congruence case needs ω to commute
-- past a word.  That is now available — Figure8.ω-central / ω^-central,
-- from the axiom Figure8.cω, which had to be added: our ω is the derived
-- word (SH)³ rather than Selinger's central generator, and without
-- centrality the width-1 fragment ⟨S , H | H² , S⁴ , (SH)²⁴⟩ is the
-- infinite von Dyck group D(4,2,24) instead of C(1).  What remains for
-- `scalars` is the induction itself, plus completeness of Figure 8 mod
-- scalars for the P4 action (Selinger.Iso, one layer down).
--
-- `ω-faithful` is a different kind of statement: the scalars have to be
-- shown NOT to collapse, which no syntactic argument gives — it wants
-- the matrix model, or another ℤ/8-valued invariant.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem

module Examples.Groups.Clifford.Qubit.Selinger.NormalForm
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Nat using (zero)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)

open import Word.Base using (Word ; ε ; _•_ ; _^_)
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
import Normalization.NormalForm.Setoid as SNF

import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic using (Gen ; S ; H ; Circuit)
-- Qualified: PrimeModulus' (in the module telescope) also exports `act`.
import Examples.Groups.Symplectic.WordAction p-2 p-prime as WA
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (_≈ˢ_ ; module Interpretation)
open Interpretation using (⟦_⟧)
open import Examples.Groups.Symplectic.Normalization.Faithful1 p-2 p-prime
  using (⟦⟧-sound)
open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime using (NF)
-- The realising circuit [ nf ] : NF n → Word (Gen n) (Selinger's N(n)) is
-- built in Normalization.Section, avoiding the WIP Surjectivity chain.
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using () renaming ([_] to nf→word)
-- The normal form itself (coset enumeration up the tower), and the
-- injectivity of its section — Selinger's Lemma 5.5 for the symplectic
-- quotient.
open import Examples.Groups.Symplectic.Normalization p-2 p-prime
  using (nfp'-sec ; nfp'-sec-agree)
open import Examples.Groups.Symplectic.Normalization.Uniqueness p-2 p-prime
  using (⟦[]⟧-injective)
-- The scalar as a SYMPLECTIC word.  Figure 8 has its own gate set now,
-- in which ω is a 0-ary generator, so its ω is a word over a different
-- alphabet; everything here is a symplectic circuit, and what it needs
-- is the word that generator names.
ω : ∀ {n} → Word (Gen (₁₊ n))
ω = (S • H) ^ 3

-- The simplified rule set, and its identification with the original one.
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
-- Transporting the simplified congruence into the original one
--
-- Theorem-Sym-iso-Sim' is an isomorphism from the simplified word group
-- to the original one whose underlying map is the identity, so its
-- congruence is exactly the implication ≈₂ ⇒ ≈₁.  Composing with
-- Faithful1.⟦⟧-sound gives soundness for the simplified rules.

private
  module Tr (m : ℕ) where
    module W₁ = Group-Lemmas (m QRel,_===₁_) (grouplike₁ {m})
    module W₂ = Group-Lemmas (m QRel,_===₂_) (grouplike₂ {m})
    open GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                        (Group.rawGroup W₁.•-ε-group)
    open IsGroupIsomorphism (Theorem-Sym-iso-Sim' {m}) public using (⟦⟧-cong)

  ≈₂⇒≈₁ : {w v : Circuit n} →
          PB._≈_ (n QRel,_===₂_) w v → PB._≈_ (n QRel,_===₁_) w v
  ≈₂⇒≈₁ {n} = Tr.⟦⟧-cong n

------------------------------------------------------------------------
-- The exact normal form (Selinger Definition 4.5)

-- An exact normal form is a symplectic normal form N(n) together with a
-- global phase ωᵖ, where p ∈ {0, 1, …, 7} (ω has order 8, relation C1).
ExactNF : (n : ℕ) → Set
ExactNF n = NF n × Fin 8

------------------------------------------------------------------------
-- Its realising circuit

-- The symplectic normal-form word, followed by the scalar ωᵖ.  (ω lives on
-- the first wire, so this needs at least one qubit.)
⟦_⟧ᴺ : ExactNF (₁₊ n) → Word (Gen (₁₊ n))
⟦ nf , p ⟧ᴺ = nf→word nf • ω ^ toℕ p

------------------------------------------------------------------------
-- The scalar ωᵖ is invisible to the symplectic (phaseless) action

-- ω = (S·H)³ acts trivially on Pauli operators.  In the simplified rule
-- set this is not an axiom but the derived Lemmas1.lemma-order-SH — at
-- p = 2 it is the statement that M₁ = ω is trivial in Sp.
act-ω : (x : _) → WA.act (ω {n}) x ≡ x
act-ω {n} x =
  Eq.trans (WA.act≡ap ((S • H) ^ 3) x)
    (Eq.trans (⟦⟧-sound (≈₂⇒≈₁ (SimL.Lemmas1.lemma-order-SH n)) x)
              (Eq.sym (WA.act≡ap ε x)))

-- Hence so does every power ωᵏ (match the 0/1/2+ shape of the word power).
act-ω^ : (k : ℕ) (x : _) → WA.act (ω {n} ^ k) x ≡ x
act-ω^ zero          x = Eq.refl
act-ω^ (suc zero)    x = act-ω x
act-ω^ (suc (suc k)) x =
  Eq.trans (Eq.cong (WA.act ω) (act-ω^ (suc k) x)) (act-ω x)

-- Therefore the exact normal form and its symplectic core have the same
-- action: the ωᵖ layer is exactly the datum the symplectic quotient forgets.
nf-act-invariant : (nf : NF (₁₊ n)) (p : Fin 8)
                 → WA.act ⟦ nf , p ⟧ᴺ ≗ WA.act (nf→word nf)
nf-act-invariant nf p x = Eq.cong (WA.act (nf→word nf)) (act-ω^ (toℕ p) x)

------------------------------------------------------------------------
-- The scalar is symplectically trivial
--
-- act-ω above is the image of a syntactic fact: in the symplectic rule
-- set ω is not merely invisible to the action, it IS the empty word.

infix 4 _≈₁_
_≈₁_ : {n : ℕ} → Circuit n → Circuit n → Set
_≈₁_ {n} = PB._≈_ (n QRel,_===₁_)

ω≈ε : ω {n} ≈₁ ε
ω≈ε {n} = ≈₂⇒≈₁ (SimL.Lemmas1.lemma-order-SH n)

ω^≈ε : (k : ℕ) → (ω {n} ^ k) ≈₁ ε
ω^≈ε zero          = PB.refl
ω^≈ε (suc zero)    = ω≈ε
ω^≈ε (suc (suc k)) = PB.trans (PB.cong ω≈ε (ω^≈ε (suc k))) PB.left-unit

-- Hence an exact normal form is, symplectically, its core.
⟦⟧ᴺ-core : (nf : NF (₁₊ n)) (p : Fin 8) → ⟦ nf , p ⟧ᴺ ≈₁ nf→word nf
⟦⟧ᴺ-core nf p = PB.trans (PB.cong PB.refl (ω^≈ε (toℕ p))) PB.right-unit

------------------------------------------------------------------------
-- Existence and uniqueness (Selinger Lemma 5.5, symplectic half)
--
-- The symplectic layer already has a normal form; what is added here is
-- its reading through nf→word, which is the form Selinger's N(n) takes.

-- The normal form of a circuit.
nfˢ : Circuit n → NF n
nfˢ {n} = SNF.NormalForm.nf (nfp'-sec n)

-- Existence: every circuit is symplectically equal to the word of its
-- normal form.  (The normal form's own section agrees with nf→word —
-- nfp'-sec-agree — so the retraction can be read over Section's [_].)
nf-existence : (w : Circuit n) → w ≈₁ nf→word (nfˢ w)
nf-existence {n} w =
  PB.trans (PB.sym (SNF.NormalForm.inv-nf∘nf=id (nfp'-sec n) {w}))
           (nfp'-sec-agree n (nfˢ w))

-- Uniqueness: normal forms with symplectically equal words are equal.
-- Soundness pushes the equation into Sp(2n,p), where the section is
-- injective (Normalization.Uniqueness).
nf-uniqueness : {u v : NF n} → nf→word u ≈₁ nf→word v → u ≡ v
nf-uniqueness {n} eq = ⟦[]⟧-injective n (⟦⟧-sound eq)

------------------------------------------------------------------------
-- The same, in the exact packaging
--
-- Every circuit has an exact normal form — with ANY scalar the caller
-- likes, since the symplectic congruence cannot see it — and the
-- symplectic component of an exact normal form is determined, while the
-- scalar component is not.  Pinning the scalar down is exactly the work
-- left to the exact (Figure-8) layer, where ω has order 8 instead of 1.

exact-existence : (w : Circuit (₁₊ n)) (p : Fin 8) → w ≈₁ ⟦ nfˢ w , p ⟧ᴺ
exact-existence w p =
  PB.trans (nf-existence w) (PB.sym (⟦⟧ᴺ-core (nfˢ w) p))

exact-uniqueness : {u v : NF (₁₊ n)} {p q : Fin 8} →
                   ⟦ u , p ⟧ᴺ ≈₁ ⟦ v , q ⟧ᴺ → u ≡ v
exact-uniqueness {u = u} {v} {p} {q} eq = nf-uniqueness
  (PB.trans (PB.sym (⟦⟧ᴺ-core u p)) (PB.trans eq (⟦⟧ᴺ-core v q)))

scalar-invisible : (u : NF (₁₊ n)) (p q : Fin 8) → ⟦ u , p ⟧ᴺ ≈₁ ⟦ u , q ⟧ᴺ
scalar-invisible u p q = PB.trans (⟦⟧ᴺ-core u p) (PB.sym (⟦⟧ᴺ-core u q))

------------------------------------------------------------------------
-- The normal form decides the symplectic word problem

nf-sound : {w v : Circuit n} → w ≈₁ v → nfˢ w ≡ nfˢ v
nf-sound {n} = SNF.NormalForm.nf-cong (nfp'-sec n)

nf-complete : {w v : Circuit n} → nfˢ w ≡ nfˢ v → w ≈₁ v
nf-complete {n} {w} {v} eq = PB.trans
  (nf-existence w)
  (PB.trans (PB.refl' (n QRel,_===₁_) (Eq.cong nf→word eq))
            (PB.sym (nf-existence v)))

------------------------------------------------------------------------
-- The symplectic part is determined by the operator
--
-- The strongest form: two exact normal forms with the same ACTION have
-- the same symplectic part.  Their scalars need not agree — the action
-- is blind to ω (act-ω), which is why the exact group needs the ℤ/8
-- layer of Qubit.ExactExtension on top of this.

act-determines-nf : {u v : NF (₁₊ n)} {p q : Fin 8} →
                    WA.act ⟦ u , p ⟧ᴺ ≗ WA.act ⟦ v , q ⟧ᴺ → u ≡ v
act-determines-nf {n} {u} {v} {p} {q} eq = ⟦[]⟧-injective (₁₊ n) claim
  where
  claim : ⟦ nf→word u ⟧ ≈ˢ ⟦ nf→word v ⟧
  claim x =
    Eq.trans (Eq.sym (WA.act≡ap (nf→word u) x))
      (Eq.trans (Eq.sym (nf-act-invariant u p x))
        (Eq.trans (eq x)
          (Eq.trans (nf-act-invariant v q x) (WA.act≡ap (nf→word v) x))))
