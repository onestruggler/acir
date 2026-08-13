{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- rel-X↓-CZ is redundant — modulo faithfulness.
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
