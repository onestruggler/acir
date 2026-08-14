{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- rel-X↓-CZ is redundant — modulo faithfulness.
--
-- SUPERSEDED by Paper-V0.Derivation, which proves the rule outright.
-- Both reductions here stop at a gap; Derivation gets past them by
-- conjugating the other way round, so that the two-wire gate alternates
-- between CZ and CX and blake-c12 supplies every crossing.  What is kept
-- below is the analysis, not the conclusion: the four facts about P are
-- still the shortest statement of WHY the rule holds, and lemma-push /
-- lemma-reduce still record how far the K-route gets.
--
-- Paper-V0 takes one Pauli-versus-CZ rule as an axiom (the other is
-- derived from it by the swap; see Paper-V0.Lemmas.lemma-rel-X↑-CZ).
-- The survivor is redundant too: a coset enumeration of the two-wire
-- presentation at p = 3, 5 and 7 gives the same index for the one-wire
-- subgroup with and without it, so the presented group is unchanged.
-- That settles the QUESTION but produces no derivation, and Agda wants a
-- proof term.  This module is how far rewriting gets, and exactly where
-- it stops.
--
-- Write P for what CZ costs when it crosses X, so that
--
--     CZ • X ≈ X • (P • CZ)                     (lemma-P)
--
-- and the axiom says P ≈ Z ↑.  Proved below, using no Pauli-versus-CZ
-- rule anywhere (see the import list — every lemma taken from
-- Paper-V0.Lemmas is named, and none of them is downstream of the
-- axiom):
--
--     P commutes with Z, Z ↑, S, S ↑            (the four facts)
--
-- In Pauli n ⋊ Sp that already forces P into ⟨Z ↑⟩: conjugation acts on
-- the Paulis through the symplectic part alone, so commuting with Z and
-- Z ↑ makes the symplectic part fix both, commuting with S and S ↑ cuts
-- the Pauli part down to ⟨Z, Z ↑⟩, and P commuting with CZ • H — which
-- blake-c12 gives, and which is not proved here — excludes the Z.  The
-- step that does NOT survive the translation into syntax is the first
-- one: it is faithfulness of the symplectic action, a fact about the
-- presented group and not a rewriting rule.  That is the record below.
--
-- The record's field asks for P ≈ Z ↑ outright, which bundles that step
-- with one more: pinning the exponent once P is known to be a power of
-- Z ↑.  That second half IS rewriting — feed P ≈ (Z ↑) ^ k through
-- Ex • X ≈ X ↑ • Ex decomposed along Ex = (CZ • H • H ↑) ³ to get
-- Z ^ (k² - 1) • X ↑ ^ (k - 1) ≈ ε, then conjugate by S ↑, which fixes Z
-- and sends X ↑ to X ↑ • Z ↑, leaving Z ↑ ^ (k - 1) ≈ ε — so it could be
-- split off into a lemma.  It is not formalised here; the exponent
-- bookkeeping (k, k², k(p-1), all mod p) is a chunk of work on its own.
-- It is the half that makes the rule true rather than merely consistent:
-- it is what fails for k = -1, the one deformation order-Ex alone allows.
--
-- The second half of the file takes the other route, and gets to a
-- SMALLER gap by a different reduction.  Decompose X into H's and S's
-- and push CZ through the six letters one at a time: the S's cost
-- nothing (lemma-comm-CZ-S), so the whole cost is four copies of one
-- unknown, K = CZ • H • CZ ⁻¹.  Pushing gives
--
--     CZ • X ≈ (K • S • K • K • S ⁻¹ • K) • CZ         (lemma-push)
--
-- and K ² is then FORCED — it is CZ • H ² • CZ ⁻¹, and H ² is the
-- multiplier by −1, which inverts the CZ it passes (lemma-K²).
-- Substituting it, and reading Z's definition backwards to collapse
-- S • M₋₁ • S ⁻¹, leaves (lemma-reduce)
--
--     K • (M₋₁ • Z) • (CZ ^ (p-2) • K) ≈ X • Z ↑       (the gap)
--
-- with two occurrences of K and nothing else unknown.  Explicit-Crossing
-- instantiates K at CZ • H • CZ ⁻¹ and shows the gap is EQUIVALENT to the
-- axiom, so nothing was thrown away on the way down.  Closing it means
-- knowing K as a word, which is exactly Simplified-V1's c11 — and
-- Paper-V0.Lemmas derives c10/c11 the other way round, out of this very
-- axiom, so it cannot be borrowed from there.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Redundancy
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen
-- Only these, and not one of them is downstream of rel-X↓-CZ:
-- lemma-comm-CZ-Z and lemma-comm-CZ-Z↑ come from order-H and the
-- multiplier, lemma-comm-CZ-S from comm-CZ-S↑ conjugated by the swap.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  p-3 p-prime g* g-gen
  using (module One-Wire ; module Paper-GroupLike ; module Ex-Conjugation)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.LemmasXZ
  p-3 p-prime g* g-gen as LXZ

open Clifford-Relations
open Lemmas-Clifford using (lemma-comm-X-w↑ ; lemma-comm-S-w↑)

module Analysis (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelˡ ; •-cancelʳ)
  open Ex-Conjugation n
    using (lemma-comm-CZ-Z ; lemma-comm-CZ-Z↑ ; lemma-comm-CZ-S)

  private
    module CL = One-Wire (₁₊ n)
    module XZ = LXZ.Lemmas1b (₁₊ n)

  ----------------------------------------------------------------------
  -- What CZ costs when it crosses X

  P : Word (Gen (₂₊ n))
  P = X ^ p-1 • (CZ • (X • CZ ^ p-1))

  private
    Xᵖ : X • X ^ p-1 ≈ ε
    Xᵖ = CL.lemma-order-X

    CZᵖ : CZ ^ p-1 • CZ ≈ ε
    CZᵖ = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p              ≈⟨ axiom order-CZ ⟩
      ε ∎

  -- P's defining property, and the only way it is used below.
  lemma-P : CZ • X ≈ X • (P • CZ)
  lemma-P = sym (begin
    X • ((X ^ p-1 • (CZ • (X • CZ ^ p-1))) • CZ)
      ≈⟨ cright assoc ⟩
    X • (X ^ p-1 • ((CZ • (X • CZ ^ p-1)) • CZ))
      ≈⟨ sym assoc ⟩
    (X • X ^ p-1) • ((CZ • (X • CZ ^ p-1)) • CZ)
      ≈⟨ cleft Xᵖ ⟩
    ε • ((CZ • (X • CZ ^ p-1)) • CZ)
      ≈⟨ left-unit ⟩
    (CZ • (X • CZ ^ p-1)) • CZ
      ≈⟨ assoc ⟩
    CZ • ((X • CZ ^ p-1) • CZ)
      ≈⟨ cright assoc ⟩
    CZ • (X • (CZ ^ p-1 • CZ))
      ≈⟨ cright cright CZᵖ ⟩
    CZ • (X • ε)
      ≈⟨ cright right-unit ⟩
    CZ • X ∎)

  ----------------------------------------------------------------------
  -- P commutes with the two Z's
  --
  -- Both proofs are the same shape: cross lemma-P from both sides and
  -- cancel the X on the left and the CZ on the right.  The Pauli passes
  -- X because X and Z commute (LemmasXZ) and passes CZ because CZ is
  -- diagonal (Ex-Conjugation).

  fact-Z : P • Z ≈ Z • P
  fact-Z = •-cancelˡ {g = X} (•-cancelʳ {h = CZ} claim)
    where
    claim : (X • (P • Z)) • CZ ≈ (X • (Z • P)) • CZ
    claim = begin
      (X • (P • Z)) • CZ    ≈⟨ assoc ⟩
      X • ((P • Z) • CZ)    ≈⟨ cright assoc ⟩
      X • (P • (Z • CZ))    ≈⟨ cright cright sym lemma-comm-CZ-Z ⟩
      X • (P • (CZ • Z))    ≈⟨ cright sym assoc ⟩
      X • ((P • CZ) • Z)    ≈⟨ sym assoc ⟩
      (X • (P • CZ)) • Z    ≈⟨ cleft sym lemma-P ⟩
      (CZ • X) • Z          ≈⟨ assoc ⟩
      CZ • (X • Z)          ≈⟨ cright XZ.lemma-comm-X-Z ⟩
      CZ • (Z • X)          ≈⟨ sym assoc ⟩
      (CZ • Z) • X          ≈⟨ cleft lemma-comm-CZ-Z ⟩
      (Z • CZ) • X          ≈⟨ assoc ⟩
      Z • (CZ • X)          ≈⟨ cright lemma-P ⟩
      Z • (X • (P • CZ))    ≈⟨ sym assoc ⟩
      (Z • X) • (P • CZ)    ≈⟨ cleft sym XZ.lemma-comm-X-Z ⟩
      (X • Z) • (P • CZ)    ≈⟨ assoc ⟩
      X • (Z • (P • CZ))    ≈⟨ cright sym assoc ⟩
      X • ((Z • P) • CZ)    ≈⟨ sym assoc ⟩
      (X • (Z • P)) • CZ ∎

  fact-Z↑ : P • Z ↑ ≈ Z ↑ • P
  fact-Z↑ = •-cancelˡ {g = X} (•-cancelʳ {h = CZ} claim)
    where
    comm-X-Z↑ : X • Z ↑ ≈ Z ↑ • X
    comm-X-Z↑ = lemma-comm-X-w↑ Z

    claim : (X • (P • Z ↑)) • CZ ≈ (X • (Z ↑ • P)) • CZ
    claim = begin
      (X • (P • Z ↑)) • CZ   ≈⟨ assoc ⟩
      X • ((P • Z ↑) • CZ)   ≈⟨ cright assoc ⟩
      X • (P • (Z ↑ • CZ))   ≈⟨ cright cright sym lemma-comm-CZ-Z↑ ⟩
      X • (P • (CZ • Z ↑))   ≈⟨ cright sym assoc ⟩
      X • ((P • CZ) • Z ↑)   ≈⟨ sym assoc ⟩
      (X • (P • CZ)) • Z ↑   ≈⟨ cleft sym lemma-P ⟩
      (CZ • X) • Z ↑         ≈⟨ assoc ⟩
      CZ • (X • Z ↑)         ≈⟨ cright comm-X-Z↑ ⟩
      CZ • (Z ↑ • X)         ≈⟨ sym assoc ⟩
      (CZ • Z ↑) • X         ≈⟨ cleft lemma-comm-CZ-Z↑ ⟩
      (Z ↑ • CZ) • X         ≈⟨ assoc ⟩
      Z ↑ • (CZ • X)         ≈⟨ cright lemma-P ⟩
      Z ↑ • (X • (P • CZ))   ≈⟨ sym assoc ⟩
      (Z ↑ • X) • (P • CZ)   ≈⟨ cleft sym comm-X-Z↑ ⟩
      (X • Z ↑) • (P • CZ)   ≈⟨ assoc ⟩
      X • (Z ↑ • (P • CZ))   ≈⟨ cright sym assoc ⟩
      X • ((Z ↑ • P) • CZ)   ≈⟨ sym assoc ⟩
      (X • (Z ↑ • P)) • CZ ∎

  ----------------------------------------------------------------------
  -- P commutes with the two phase gates
  --
  -- S ↑ is the easy one: it passes X and CZ outright.  S is not — it
  -- turns X into X • Z (conj-S-X) — so what falls out first is that P
  -- commutes with Z • S, and fact-Z then peels the Z off.

  fact-S↑ : P • S ↑ ≈ S ↑ • P
  fact-S↑ = •-cancelˡ {g = X} (•-cancelʳ {h = CZ} claim)
    where
    comm-X-S↑ : X • S ↑ ≈ S ↑ • X
    comm-X-S↑ = lemma-comm-X-w↑ S

    claim : (X • (P • S ↑)) • CZ ≈ (X • (S ↑ • P)) • CZ
    claim = begin
      (X • (P • S ↑)) • CZ   ≈⟨ assoc ⟩
      X • ((P • S ↑) • CZ)   ≈⟨ cright assoc ⟩
      X • (P • (S ↑ • CZ))   ≈⟨ cright cright sym (axiom comm-CZ-S↑) ⟩
      X • (P • (CZ • S ↑))   ≈⟨ cright sym assoc ⟩
      X • ((P • CZ) • S ↑)   ≈⟨ sym assoc ⟩
      (X • (P • CZ)) • S ↑   ≈⟨ cleft sym lemma-P ⟩
      (CZ • X) • S ↑         ≈⟨ assoc ⟩
      CZ • (X • S ↑)         ≈⟨ cright comm-X-S↑ ⟩
      CZ • (S ↑ • X)         ≈⟨ sym assoc ⟩
      (CZ • S ↑) • X         ≈⟨ cleft axiom comm-CZ-S↑ ⟩
      (S ↑ • CZ) • X         ≈⟨ assoc ⟩
      S ↑ • (CZ • X)         ≈⟨ cright lemma-P ⟩
      S ↑ • (X • (P • CZ))   ≈⟨ sym assoc ⟩
      (S ↑ • X) • (P • CZ)   ≈⟨ cleft sym comm-X-S↑ ⟩
      (X • S ↑) • (P • CZ)   ≈⟨ assoc ⟩
      X • (S ↑ • (P • CZ))   ≈⟨ cright sym assoc ⟩
      X • ((S ↑ • P) • CZ)   ≈⟨ sym assoc ⟩
      (X • (S ↑ • P)) • CZ ∎

  private
    fact-ZS : P • (Z • S) ≈ (Z • S) • P
    fact-ZS = •-cancelˡ {g = X} (•-cancelʳ {h = CZ} claim)
      where
      claim : (X • (P • (Z • S))) • CZ ≈ (X • ((Z • S) • P)) • CZ
      claim = begin
        (X • (P • (Z • S))) • CZ
          ≈⟨ assoc ⟩
        X • ((P • (Z • S)) • CZ)
          ≈⟨ cright assoc ⟩
        X • (P • ((Z • S) • CZ))
          ≈⟨ cright cright assoc ⟩
        X • (P • (Z • (S • CZ)))
          ≈⟨ cright cright cright sym lemma-comm-CZ-S ⟩
        X • (P • (Z • (CZ • S)))
          ≈⟨ cright cright sym assoc ⟩
        X • (P • ((Z • CZ) • S))
          ≈⟨ cright cright cleft sym lemma-comm-CZ-Z ⟩
        X • (P • ((CZ • Z) • S))
          ≈⟨ cright cright assoc ⟩
        X • (P • (CZ • (Z • S)))
          ≈⟨ cright sym assoc ⟩
        X • ((P • CZ) • (Z • S))
          ≈⟨ sym assoc ⟩
        (X • (P • CZ)) • (Z • S)
          ≈⟨ cleft sym lemma-P ⟩
        (CZ • X) • (Z • S)
          ≈⟨ assoc ⟩
        CZ • (X • (Z • S))
          ≈⟨ cright sym assoc ⟩
        CZ • ((X • Z) • S)
          ≈⟨ cright sym XZ.conj-S-X ⟩
        CZ • (S • X)
          ≈⟨ sym assoc ⟩
        (CZ • S) • X
          ≈⟨ cleft lemma-comm-CZ-S ⟩
        (S • CZ) • X
          ≈⟨ assoc ⟩
        S • (CZ • X)
          ≈⟨ cright lemma-P ⟩
        S • (X • (P • CZ))
          ≈⟨ sym assoc ⟩
        (S • X) • (P • CZ)
          ≈⟨ cleft XZ.conj-S-X ⟩
        ((X • Z) • S) • (P • CZ)
          ≈⟨ cleft assoc ⟩
        (X • (Z • S)) • (P • CZ)
          ≈⟨ assoc ⟩
        X • ((Z • S) • (P • CZ))
          ≈⟨ cright sym assoc ⟩
        X • (((Z • S) • P) • CZ)
          ≈⟨ sym assoc ⟩
        (X • ((Z • S) • P)) • CZ ∎

  fact-S : P • S ≈ S • P
  fact-S = •-cancelˡ {g = Z} claim
    where
    claim : Z • (P • S) ≈ Z • (S • P)
    claim = begin
      Z • (P • S)    ≈⟨ sym assoc ⟩
      (Z • P) • S    ≈⟨ cleft sym fact-Z ⟩
      (P • Z) • S    ≈⟨ assoc ⟩
      P • (Z • S)    ≈⟨ fact-ZS ⟩
      (Z • S) • P    ≈⟨ assoc ⟩
      Z • (S • P) ∎

------------------------------------------------------------------------
-- The gap
--
-- Two things are bundled into the single field, and neither is a
-- rewriting step.
--
-- FAITHFULNESS.  The four facts say P commutes with Z, Z ↑, S and S ↑.
-- In Pauli n ⋊ Sp that puts P in ⟨Z, Z ↑⟩ — conjugation acts on the
-- Paulis through the symplectic part alone, and Sp acts faithfully, so
-- commuting with all the Paulis makes P one of them, and commuting with
-- S and S ↑ then cuts it down.  Adding that P commutes with CZ • H,
-- which blake-c12 gives, excludes the Z and leaves ⟨Z ↑⟩.  Faithfulness
-- is a fact about the presented group, not a rule of the congruence:
-- in the axiom-free presentation the centraliser of the Paulis could a
-- priori be larger, and that it is not is what the coset enumeration
-- checks.
--
-- THE EXPONENT.  From P ≈ (Z ↑) ^ k, feeding lemma-P through
-- Ex • X ≈ X ↑ • Ex decomposed along Ex = (CZ • H • H ↑) ³ gives
-- Z ^ (k² - 1) • X ↑ ^ (k - 1) ≈ ε; conjugating by S ↑, which fixes Z
-- and sends X ↑ to X ↑ • Z ↑, leaves Z ↑ ^ (k - 1) ≈ ε and hence
-- (Z ↑) ^ k ≈ Z ↑.  This half IS rewriting, and it is what makes the
-- rule true rather than merely consistent — it is the step that fails
-- for k = -1, the one deformation order-Ex alone would allow.  It is
-- not formalised here.

record Faithful : Set where
  field
    lemma-P≈Z↑ : ∀ {n} → let open PB ((₂₊ n) QRel,_===_) using (_≈_) in
                 Analysis.P n ≈ Z ↑

------------------------------------------------------------------------
-- …and the axiom, given it

module Theorem (fd : Faithful) where

  open Faithful fd

  lemma-rel-X↓-CZ : ∀ {n} → let open PB ((₂₊ n) QRel,_===_) using (_≈_) in
                    CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
  lemma-rel-X↓-CZ {n} = begin
    CZ • X               ≈⟨ Analysis.lemma-P n ⟩
    X • (P • CZ)         ≈⟨ cright cleft lemma-P≈Z↑ ⟩
    X • (Z ↑ • CZ) ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Analysis n using (P)

------------------------------------------------------------------------
-- The other decomposition: push CZ through X letter by letter
--
-- X = H • S • H • H • S ⁻¹ • H, and CZ crosses S and S ⁻¹ outright
-- (comm-CZ-S↑ conjugated by the swap).  So the ONLY thing missing is
-- what CZ costs when it crosses a single H, and that cost is used four
-- times.  Everything below is parametric in it: K is whatever
--
--     CZ • H ≈ K • CZ
--
-- produces — K is CZ • H • CZ ⁻¹, so it always exists, and naming it
-- turns the axiom into a statement about K alone.
--
-- Two things then come for free.  Pushing CZ through all six letters
-- gives lemma-push, and K ^ 2 is forced: it is CZ • H ^ 2 • CZ ⁻¹, and
-- H ^ 2 is the multiplier by −1, which inverts the CZ it passes.  So the
-- axiom reduces to lemma-gap below — one equation, two occurrences of K,
-- no CZ left on either side except the one K ² leaves behind.
--
-- Filling that in is what remains.  The K in it is opaque: what it is
-- as a word is precisely Simplified-V1's c11, which Paper-V0 does not
-- have (Paper-V0.Lemmas derives c10/c11 the other way round, out of
-- this very axiom).

module Crossing (n : ℕ)
                (K : Word (Gen (₂₊ n)))
                (let open PB ((₂₊ n) QRel,_===_))
                (cross : CZ • H ≈ K • CZ) where

  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ)
  open Ex-Conjugation n using (lemma-comm-CZ-S ; lemma-CZ-M₋₁ ; Z-split ; e₁)

  private
    module CL = One-Wire (₁₊ n)

    -- CZ crosses a phase gate, and a phase gate's inverse, untouched.
    cross-S : CZ • S ≈ S • CZ
    cross-S = lemma-comm-CZ-S

    cross-S⁻¹ : CZ • S⁻¹ ≈ S⁻¹ • CZ
    cross-S⁻¹ = comm⇒pow-comm 1 p-1 lemma-comm-CZ-S

  ----------------------------------------------------------------------
  -- Six letters, four crossings

  lemma-push : CZ • X ≈ (K • (S • (K • (K • (S⁻¹ • K))))) • CZ
  lemma-push = begin
    CZ • (H • (S • (H • (H • (S⁻¹ • H)))))
      ≈⟨ sym assoc ⟩
    (CZ • H) • (S • (H • (H • (S⁻¹ • H))))
      ≈⟨ cleft cross ⟩
    (K • CZ) • (S • (H • (H • (S⁻¹ • H))))
      ≈⟨ assoc ⟩
    K • (CZ • (S • (H • (H • (S⁻¹ • H)))))
      ≈⟨ cright sym assoc ⟩
    K • ((CZ • S) • (H • (H • (S⁻¹ • H))))
      ≈⟨ cright cleft cross-S ⟩
    K • ((S • CZ) • (H • (H • (S⁻¹ • H))))
      ≈⟨ cright assoc ⟩
    K • (S • (CZ • (H • (H • (S⁻¹ • H)))))
      ≈⟨ cright cright sym assoc ⟩
    K • (S • ((CZ • H) • (H • (S⁻¹ • H))))
      ≈⟨ cright cright cleft cross ⟩
    K • (S • ((K • CZ) • (H • (S⁻¹ • H))))
      ≈⟨ cright cright assoc ⟩
    K • (S • (K • (CZ • (H • (S⁻¹ • H)))))
      ≈⟨ cright cright cright sym assoc ⟩
    K • (S • (K • ((CZ • H) • (S⁻¹ • H))))
      ≈⟨ cright cright cright cleft cross ⟩
    K • (S • (K • ((K • CZ) • (S⁻¹ • H))))
      ≈⟨ cright cright cright assoc ⟩
    K • (S • (K • (K • (CZ • (S⁻¹ • H)))))
      ≈⟨ cright cright cright cright sym assoc ⟩
    K • (S • (K • (K • ((CZ • S⁻¹) • H))))
      ≈⟨ cright cright cright cright cleft cross-S⁻¹ ⟩
    K • (S • (K • (K • ((S⁻¹ • CZ) • H))))
      ≈⟨ cright cright cright cright assoc ⟩
    K • (S • (K • (K • (S⁻¹ • (CZ • H)))))
      ≈⟨ cright cright cright cright cright cross ⟩
    K • (S • (K • (K • (S⁻¹ • (K • CZ)))))
      ≈⟨ cright cright cright cright sym assoc ⟩
    K • (S • (K • (K • ((S⁻¹ • K) • CZ))))
      ≈⟨ cright cright cright sym assoc ⟩
    K • (S • (K • ((K • (S⁻¹ • K)) • CZ)))
      ≈⟨ cright cright sym assoc ⟩
    K • (S • ((K • (K • (S⁻¹ • K))) • CZ))
      ≈⟨ cright sym assoc ⟩
    K • ((S • (K • (K • (S⁻¹ • K)))) • CZ)
      ≈⟨ sym assoc ⟩
    (K • (S • (K • (K • (S⁻¹ • K))))) • CZ ∎

  ----------------------------------------------------------------------
  -- The square of the crossing is forced
  --
  -- K ² is CZ • H ² • CZ ⁻¹, and H ² is the multiplier by −1, which
  -- inverts the CZ it passes — so K ² is M₋₁ with a CZ-power attached.

  private
    e₁≡ : e₁ ≡ p-1
    e₁≡ = lemma-toℕ-1ₚ

    CZᵉ : CZ ^ e₁ ≈ CZ ^ p-2 • CZ
    CZᵉ = begin
      CZ ^ e₁             ≡⟨ Eq.cong (CZ ^_) e₁≡ ⟩
      CZ ^ p-1            ≡⟨ Eq.cong (CZ ^_) (NP.+-comm 1 p-2) ⟩
      CZ ^ (p-2 Nat.+ 1)  ≈⟨ ^-+ CZ p-2 1 ⟩
      CZ ^ p-2 • CZ ∎

  lemma-K² : K • K ≈ M₋₁ • CZ ^ p-2
  lemma-K² = •-cancelʳ {h = CZ} (begin
    (K • K) • CZ
      ≈⟨ assoc ⟩
    K • (K • CZ)
      ≈⟨ cright sym cross ⟩
    K • (CZ • H)
      ≈⟨ sym assoc ⟩
    (K • CZ) • H
      ≈⟨ cleft sym cross ⟩
    (CZ • H) • H
      ≈⟨ assoc ⟩
    CZ • (H • H)
      ≈⟨ cright axiom order-H ⟩
    CZ • M₋₁
      ≈⟨ lemma-CZ-M₋₁ ⟩
    M₋₁ • CZ ^ e₁
      ≈⟨ cright CZᵉ ⟩
    M₋₁ • (CZ ^ p-2 • CZ)
      ≈⟨ sym assoc ⟩
    (M₋₁ • CZ ^ p-2) • CZ ∎)

  ----------------------------------------------------------------------
  -- …so the axiom is this one equation

  private
    -- S conjugates the multiplier by −1 into itself times a Z; this is
    -- Z's definition read backwards.
    S-M₋₁ : S • (M₋₁ • S⁻¹) ≈ M₋₁ • Z
    S-M₋₁ = begin
      S • (M₋₁ • S⁻¹)
        ≈⟨ sym left-unit ⟩
      ε • (S • (M₋₁ • S⁻¹))
        ≈⟨ cleft sym (CL.lemma-M₋₁^2) ⟩
      (M₋₁ • M₋₁) • (S • (M₋₁ • S⁻¹))
        ≈⟨ assoc ⟩
      M₋₁ • (M₋₁ • (S • (M₋₁ • S⁻¹)))
        ≈⟨ cright sym Z-split ⟩
      M₋₁ • Z ∎

  -- The reduced form: two occurrences of the unknown crossing, and
  -- nothing else that is not already derivable.
  lemma-reduce : K • (S • (K • (K • (S⁻¹ • K))))
               ≈ K • ((M₋₁ • Z) • (CZ ^ p-2 • K))
  lemma-reduce = begin
    K • (S • (K • (K • (S⁻¹ • K))))
      ≈⟨ cright cright sym assoc ⟩
    K • (S • ((K • K) • (S⁻¹ • K)))
      ≈⟨ cright cright cleft lemma-K² ⟩
    K • (S • ((M₋₁ • CZ ^ p-2) • (S⁻¹ • K)))
      ≈⟨ cright cright assoc ⟩
    K • (S • (M₋₁ • (CZ ^ p-2 • (S⁻¹ • K))))
      ≈⟨ cright cright cright sym assoc ⟩
    K • (S • (M₋₁ • ((CZ ^ p-2 • S⁻¹) • K)))
      ≈⟨ cright cright cright cleft comm⇒pow-comm p-2 p-1 lemma-comm-CZ-S ⟩
    K • (S • (M₋₁ • ((S⁻¹ • CZ ^ p-2) • K)))
      ≈⟨ cright cright cright assoc ⟩
    K • (S • (M₋₁ • (S⁻¹ • (CZ ^ p-2 • K))))
      ≈⟨ cright cright sym assoc ⟩
    K • (S • ((M₋₁ • S⁻¹) • (CZ ^ p-2 • K)))
      ≈⟨ cright sym assoc ⟩
    K • ((S • (M₋₁ • S⁻¹)) • (CZ ^ p-2 • K))
      ≈⟨ cright cleft S-M₋₁ ⟩
    K • ((M₋₁ • Z) • (CZ ^ p-2 • K)) ∎

  ----------------------------------------------------------------------
  -- GAP.  Everything above is proved; this is what is left.
  --
  --   K • ((M₋₁ • Z) • (CZ ^ (p-2) • K)) ≈ X • Z ↑
  --
  -- Both sides are the conjugate of X by CZ: the left is what the push
  -- produced, the right is what the axiom claims.  It cannot be closed
  -- without knowing K as a word — which is Simplified-V1's c11.

  module From-Gap
    (gap : K • ((M₋₁ • Z) • (CZ ^ p-2 • K)) ≈ X • Z ↑) where

    lemma-rel-X↓-CZ : CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
    lemma-rel-X↓-CZ = begin
      CZ • X
        ≈⟨ lemma-push ⟩
      (K • (S • (K • (K • (S⁻¹ • K))))) • CZ
        ≈⟨ cleft lemma-reduce ⟩
      (K • ((M₋₁ • Z) • (CZ ^ p-2 • K))) • CZ
        ≈⟨ cleft gap ⟩
      (X • Z ↑) • CZ
        ≈⟨ assoc ⟩
      X • (Z ↑ • CZ) ∎

------------------------------------------------------------------------
-- The crossing exists, so the gap is a closed statement
--
-- Crossing is parametric in K only so that the four uses of it stay
-- visibly the same word.  Instantiating it at the obvious witness
-- K₀ = CZ • H • CZ ⁻¹ turns lemma-gap into an equation with no
-- parameters left, and the two directions below say it is EQUIVALENT to
-- the axiom — the reduction throws nothing away.

module Explicit-Crossing (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ)

  K₀ : Word (Gen (₂₊ n))
  K₀ = CZ • (H • CZ ^ p-1)

  private
    CZᵖ : CZ ^ p-1 • CZ ≈ ε
    CZᵖ = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p              ≈⟨ axiom order-CZ ⟩
      ε ∎

  cross₀ : CZ • H ≈ K₀ • CZ
  cross₀ = sym (begin
    (CZ • (H • CZ ^ p-1)) • CZ   ≈⟨ assoc ⟩
    CZ • ((H • CZ ^ p-1) • CZ)   ≈⟨ cright assoc ⟩
    CZ • (H • (CZ ^ p-1 • CZ))   ≈⟨ cright cright CZᵖ ⟩
    CZ • (H • ε)                 ≈⟨ cright right-unit ⟩
    CZ • H ∎)

  module C = Crossing n K₀ cross₀

  -- The gap, with nothing free in it.
  Gap : Set
  Gap = K₀ • ((M₋₁ • Z) • (CZ ^ p-2 • K₀)) ≈ X • Z ↑

  -- Gap ⇒ axiom.
  from-gap : Gap → CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
  from-gap gap = C.From-Gap.lemma-rel-X↓-CZ gap

  -- Axiom ⇒ Gap: nothing was lost on the way down.  (This is the ONLY
  -- place in the file that uses rel-X↓-CZ.)
  to-gap : Gap
  to-gap = •-cancelʳ {h = CZ} (begin
    (K₀ • ((M₋₁ • Z) • (CZ ^ p-2 • K₀))) • CZ
      ≈⟨ cleft sym C.lemma-reduce ⟩
    (K₀ • (S • (K₀ • (K₀ • (S⁻¹ • K₀))))) • CZ
      ≈⟨ sym C.lemma-push ⟩
    CZ • X
      ≈⟨ axiom rel-X↓-CZ ⟩
    X • (Z ↑ • CZ)
      ≈⟨ sym assoc ⟩
    (X • Z ↑) • CZ ∎)
