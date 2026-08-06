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
-- This file introduces the exact normal form and its realising circuit.
-- Exact existence and uniqueness (Lemma 5.5 with the scalar) then combine
-- the symplectic result above with the ℤ/8 ω-layer.
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

import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic using (Gen ; S ; H ; Circuit)
-- Qualified: PrimeModulus' (in the module telescope) also exports `act`.
import Examples.Groups.Symplectic.WordAction p-2 p-prime as WA
open import Examples.Groups.Symplectic.Normalization.Faithful1 p-2 p-prime
  using (⟦⟧-sound)
open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime using (NF)
-- The realising circuit [ nf ] : NF n → Word (Gen n) (Selinger's N(n)) is
-- built in Normalization.Section, avoiding the WIP Surjectivity chain.
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
  using () renaming ([_] to nf→word)
open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime using (ω)

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
