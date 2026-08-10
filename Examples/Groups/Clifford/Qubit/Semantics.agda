------------------------------------------------------------------------
-- Presentations of groups
--
-- The scalar layer of the n-qubit Clifford group (p = 2), semantic side:
--
--     1 ─→ ⟨ω⟩ ─→ Exact n ─→ CMS n ─→ 1
--
-- Exact n is the Clifford group itself; the layer below it, the
-- non-split extension 1 → Pauli n → CMS n → Sp(2n, 2) → 1 presenting the
-- Clifford group modulo scalars, is
-- Examples.Groups.ProjectiveClifford.Qubit.Semantics, from which CMS-group
-- is taken here.
--
-- ⟨ω⟩ ≅ ℤ/8, written additively in the exponent of ω: ωʲ · ωᵏ = ω^{j+k}.
-- The extension is an ordinary one, assembled by hand exactly as the
-- layer below is: the total group is Clifford words modulo the *exact*
-- congruence — the one Selinger's Figure 8 presents, which unlike ≈ᶜ
-- still sees the global scalar — with incl k = ωᵏ and proj the identity
-- on words.  See Qubit.ExactExtension, and the note at the end of this
-- file for what it still takes as input and why the P4-action cannot
-- supply it.
--
-- The scalar layer needs at least one qubit, ω living on the first wire.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Semantics where

open import Notations using (₁₊)

open import ForStdlib.Algebra.Construct.Extension using (Extension)

open import Examples.Groups.ProjectiveClifford.Qubit.Semantics
  using (CMS-group)

open import Examples.Groups.Clifford.Qubit.ExactExtension
  using (Scalar-group ; Exact-group ; ExactData)
  renaming (Exact to Exact-of)

------------------------------------------------------------------------
-- The scalars ⟨ω⟩, and the exact Clifford group

-- 1 → ⟨ω⟩ → Exact n → CMS n → 1.
Exact : ∀ {n} → ExactData n → Extension Scalar-group (CMS-group (₁₊ n))
Exact = Exact-of

------------------------------------------------------------------------
-- What Exact n still takes as input
--
-- The group structure of the Figure-8 words, that k ↦ ωᵏ is a
-- homomorphism ℤ/8 → Exact n, surjectivity of proj and that proj kills
-- the scalars are all proved in Qubit.ExactExtension.  So `Exact` is a
-- definition, not a hole; what remains is to supply one ExactData n, and
-- its three fields are Selinger's theorems rather than bookkeeping:
--
--   sound      — Figure-8-equal words act equally on P4;
--   scalars    — a word acting trivially on P4 is some ωᵏ;
--   ω-faithful — ω has order exactly 8 in the presented group.
--
-- `sound` is within reach: Selinger.Action already discharges C1, C2, C3,
-- C5-C9, C12 and C13, and C4 is an identity, leaving C10, C11, C14, C15.
--
-- The other two cannot come from the action, and ExactExtension.
-- action-blind makes that precise: ω acts trivially on P4
-- (Selinger.Action.cact-ω), so if ≈ᶜ implied the Figure-8 congruence then
-- ω = ω¹ and ε = ω⁰ would be identified and ω-faithful would force
-- ₁ ≡ ₀.  The scalar is exactly the datum cact discards, so ω-faithful
-- has to come from a faithful model of the exact Clifford group.  The two
-- candidates in reach are Selinger's exact normal form
-- (Qubit.Selinger.NormalForm, ExactNF n = NF n × Fin 8, uniqueness still
-- WIP) and matrices over ℤ[1/√2, i].
--
-- Group-theoretically the extension is the non-split 2^{1+2n}·Sp(2n,2);
-- in particular a direct product ℤ/8 × CMS n would be the wrong
-- group, which is why the scalar cannot simply be adjoined.
