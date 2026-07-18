------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger steps 3–4 (§4–5): the exact normal form for Clifford circuits.
--
-- The symplectic (phaseless) normal form N(n) — Selinger's Definitions
-- 4.3–4.4 and Lemma 5.5 — is already formalised in the ExtendedGate
-- layer:
--
--   * NF n              the normal-form data (Symplectic.Normalization.NF)
--   * nf→word : NF n → Word (Gen n)   the realising circuit; it satisfies
--       nf→word (nf , lm) = nf→word nf ↑ • [ lm ]ˡᵐ,
--     which is exactly Selinger's recursion N(n) = (N(n-1) ⊗ I)·M(n)·L(n)
--     with [ lm ]ˡᵐ = M(n)·L(n) built from the convenient gates A–E of
--     Figure 1;
--   * surjective : every symplectic map is realised by nf→word of some NF.
--
-- Selinger's *exact* normal form (Definition 4.5) is this word followed by
-- a global scalar ωᵖ, p ∈ {0,…,7}.  Under conjugation ω is invisible (it
-- is the ℤ/8 datum the ℤ/4 action `cact` cannot see — see Selinger.Action),
-- so it is exactly the extra parameter distinguishing the *exact* Clifford
-- group C(n) from its symplectic quotient Sp(2n,2).
--
-- This file introduces the exact normal form and its realising circuit.
-- Exact existence and uniqueness (Lemma 5.5 with the scalar) then combine
-- the symplectic result above with the ℤ/8 ω-layer.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.NormalForm
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Nat using (zero ; suc)
open import Data.Fin using (Fin ; toℕ)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≗_)

open import Notations
open import Word.Base using (Word ; ε ; _•_ ; _^_)

open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime
open Symplectic-Derived-Gen using (Gen ; S ; H ; SH ; srel ; order-SH)
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
  using (act)
open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime
  using (act-sound-ax)
open import Examples.Groups.Symplectic.Normalization.NF p-2 p-prime using (NF)
-- The realising circuit [ nf ] : NF n → Word (Gen n) (Selinger's N(n)) is
-- built in Normalization.Section, avoiding the WIP Surjectivity chain.
open import Examples.Groups.Symplectic.ExtendedGate.Normalization.Section p-2 p-prime
  using () renaming ([_] to nf→word)
open import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime using (ω)

private
  variable
    n : ℕ

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

-- ω = (S·H)³ acts trivially on Pauli operators (relation order-SH).
act-ω : (x : _) → act (ω {n}) x ≡ x
act-ω = act-sound-ax ((S • H) ^ 3) ε (srel order-SH)

-- Hence so does every power ωᵏ (match the 0/1/2+ shape of the word power).
act-ω^ : (k : ℕ) (x : _) → act (ω {n} ^ k) x ≡ x
act-ω^ zero          x = Eq.refl
act-ω^ (suc zero)    x = act-ω x
act-ω^ (suc (suc k)) x = Eq.trans (Eq.cong (act ω) (act-ω^ (suc k) x)) (act-ω x)

-- Therefore the exact normal form and its symplectic core have the same
-- action: the ωᵖ layer is exactly the datum the symplectic quotient forgets.
nf-act-invariant : (nf : NF (₁₊ n)) (p : Fin 8)
                 → act ⟦ nf , p ⟧ᴺ ≗ act (nf→word nf)
nf-act-invariant nf p x = Eq.cong (act (nf→word nf)) (act-ω^ (toℕ p) x)
