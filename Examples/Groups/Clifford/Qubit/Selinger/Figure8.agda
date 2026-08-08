------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's presentation of the n-qubit Clifford operators
-- (arXiv:1310.6813, Figure 8), formalised in our Circuit framework.
--
-- Generators: H, S (∈ Gate 1), CZ (∈ Gate 2), and the scalar ω, which is
-- a *derived* one-qubit word ω = SHSHSH (Selinger's relation C4).  The
-- Pauli operators are the derived words X = HSSH, Z = SS.
--
-- Relations C1–C15 (Figure 8):
--   (a) n ≥ 0 : ω⁸ = 1                                          (C1)
--   (b) n ≥ 1 : H² = 1, S⁴ = 1, SHSHSH = ω (an identity here)   (C2–C4)
--   (c) n ≥ 2 : CZ² = 1; S commutes with CZ (either wire);      (C5–C7)
--               X-through-CZ picks up a Z (either wire);        (C8, C9)
--               CZ·H·CZ = … · ω⁻¹                               (C10, C11)
--   (d) n ≥ 3 : CZ↑·CZ = CZ·CZ↑, and three more                 (C12–C15)
--
-- ... plus one relation that is not in Selinger's numbered list because
-- there it needs no stating: ω is CENTRAL (cω below).  Selinger's ω is a
-- generator, and a scalar generator commutes with everything by fiat;
-- ours is the derived word (SH)³, so centrality has to be an axiom.
-- Without it the presentation is too weak — at width 1 the relations are
-- exactly C1–C4, i.e. ⟨S , H | H² , S⁴ , (SH)²⁴⟩, the von Dyck group
-- D(4,2,24), which is infinite (¼ + ½ + ¹⁄₂₄ < 1), whereas C(1) has
-- order 192.  With a central ω of order 8 the width-1 quotient by ⟨ω⟩ is
-- ⟨S , H | H² , S⁴ , (SH)³⟩ ≅ S₄, and 24 · 8 = 192.
--
-- cω is sound for the P4-action (Selinger.Soundness.cω-sound): ω acts as
-- the identity there, so both sides act as the gate does.  It is also
-- invisible modulo scalars, where ω = 1 — Figure8-Mod-Scalar derives its
-- instance rather than assuming it.
--
-- This is the *exact* Clifford group (with the order-8 scalar ω and
-- S⁴ = 1, not the phaseless S² = 1 of the symplectic quotient).  The
-- structural rules (cong↑, comm₁, comm₂) come from Lift-Relation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Selinger.Figure8
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic
  using (Gen ; SympGate ; _↑ ; _↓ ; S ; H ; CZ ; ⊤⊥ ; ⊥⊤)

-- CRel and the structural rules come straight from the circuit framework
-- that Symplectic itself is built on (it keeps its copy private).
open import Circuit.Base SympGate using (CRel ; module Lift-Relation)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Derived words: the scalar ω and the Pauli operators X, Z

-- SH, the one-qubit word S·H.
SH : Word (Gen (₁₊ n))
SH = S • H

-- ω = SHSHSH = (SH)³ (Selinger C4, taken as a definition).
ω : Word (Gen (₁₊ n))
ω = SH ^ 3

-- ω has order 8, so ω⁻¹ = ω⁷.
ω⁻¹ : Word (Gen (₁₊ n))
ω⁻¹ = ω ^ 7

-- X = HSSH, Z = SS  (Selinger §4).
X : Word (Gen (₁₊ n))
X = H • S ^ 2 • H

Z : Word (Gen (₁₊ n))
Z = S ^ 2

------------------------------------------------------------------------
-- The Figure-8 relations

infix 4 _Sel,_===_

data _Sel,_===_ : (n : ℕ) → CRel n where

  -- (a) n ≥ 0
  c1  : ∀ {n} → (₁₊ n) Sel,  ω ^ 8 === ε

  -- (b) n ≥ 1
  c2  : ∀ {n} → (₁₊ n) Sel,  H ^ 2 === ε
  c3  : ∀ {n} → (₁₊ n) Sel,  S ^ 4 === ε

  -- C4 defines the scalar.  Since ω is a derived word here and not a
  -- generator, the relation is an identity — `axiom c4` and `refl` prove
  -- the same thing, and adding it does not change the presented group.
  -- It is stated all the same, so that the constructors track Figure 8's
  -- numbering and match Qubit.Selinger.Figure8-Mod-Scalar, where the
  -- same relation reads SHSHSH = 1 and is the quotient map.
  c4  : ∀ {n} → (₁₊ n) Sel,  SH ^ 3 === ω

  -- (c) n ≥ 2
  c5  : ∀ {n} → (₂₊ n) Sel,  CZ ^ 2 === ε
  c6  : ∀ {n} → (₂₊ n) Sel,  S ↓ • CZ === CZ • S ↓
  c7  : ∀ {n} → (₂₊ n) Sel,  S ↑ • CZ === CZ • S ↑
  c8  : ∀ {n} → (₂₊ n) Sel,  X ↓ • CZ === CZ • X ↓ • Z ↑
  c9  : ∀ {n} → (₂₊ n) Sel,  X ↑ • CZ === CZ • Z ↓ • X ↑
  c10 : ∀ {n} → (₂₊ n) Sel,  CZ • H ↑ • CZ ===
                             SH ↑ • CZ • (S • H • S) ↑ • S ↓ • ω⁻¹
  c11 : ∀ {n} → (₂₊ n) Sel,  CZ • H ↓ • CZ ===
                             SH ↓ • CZ • (S • H • S) ↓ • S ↑ • ω⁻¹

  -- The scalar is central.  One instance per generator; centrality for
  -- whole words follows (ω-central below).
  cω  : ∀ {n} (g : Gen (₁₊ n)) → (₁₊ n) Sel,  ω • [ g ]ʷ === [ g ]ʷ • ω

  -- The scalar does not depend on the wire it is written on.  Selinger
  -- has one generator ω for all widths; here ω is (SH)³ on wire 0, so
  -- ω ↑ — the same word one wire up — is a syntactically different term
  -- naming the same scalar, and they have to be identified.
  cω↑ : ∀ {n} → (₂₊ n) Sel,  ω ↑ === ω

  -- (d) n ≥ 3
  c12 : ∀ {n} → (₃₊ n) Sel,  CZ ↑ • CZ === CZ • CZ ↑
  c13 : ∀ {n} → (₃₊ n) Sel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  c14 : ∀ {n} → (₃₊ n) Sel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  c15 : ∀ {n} → (₃₊ n) Sel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

------------------------------------------------------------------------
-- The full relation, with the structural rules srel/cong↑/comm₁/comm₂.

open Lift-Relation _Sel,_===_ public

infix 4 _CRel,_===_
_CRel,_===_ : (n : ℕ) → CRel n
_CRel,_===_ = _VRel,_===_

------------------------------------------------------------------------
-- The scalar is central
--
-- cω gives it for the generators; a word commutes with ω because each of
-- its letters does.  (ε and _•_ are the two other cases: the empty word
-- by the unit laws, a concatenation by walking ω across both halves.)

infix 4 _≈ᶠ_
_≈ᶠ_ : {n : ℕ} → Word (Gen n) → Word (Gen n) → Set
_≈ᶠ_ {n} = PB._≈_ (n CRel,_===_)

ω-central : (w : Word (Gen (₁₊ n))) → (ω • w) ≈ᶠ (w • ω)
ω-central [ g ]ʷ  = PB.axiom (srel (cω g))
ω-central ε       = PB.trans PB.right-unit (PB.sym PB.left-unit)
ω-central (w • v) =
  PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (ω-central w) PB.refl)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl (ω-central v)) (PB.sym PB.assoc))))

-- Hence so does every power of ω: the scalars are a central subgroup.
ω^-central : (k : ℕ) (w : Word (Gen (₁₊ n))) → ((ω ^ k) • w) ≈ᶠ (w • (ω ^ k))
ω^-central ₀       w = PB.trans PB.left-unit (PB.sym PB.right-unit)
ω^-central (₁₊ ₀)  w = ω-central w
ω^-central (₂₊ k)  w =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (ω^-central (₁₊ k) w))
      (PB.trans (PB.sym PB.assoc)
        (PB.trans (PB.cong (ω-central w) PB.refl) PB.assoc)))

------------------------------------------------------------------------
-- The scalar is the same on every wire
--
-- cω↑ says it for ω; powers follow, because _↑ (a wmap) distributes over
-- concatenation and hence over powers.

ω↑≈ω : ((ω {n}) ↑) ≈ᶠ ω
ω↑≈ω = PB.axiom (srel cω↑)

-- (w ^ k) ↑ = (w ↑) ^ k, on the nose.
↑-^ : (w : Word (Gen n)) (k : ℕ) → (w ^ k) ↑ ≡ (w ↑) ^ k
↑-^ w ₀      = Eq.refl
↑-^ w (₁₊ ₀) = Eq.refl
↑-^ w (₂₊ k) = Eq.cong ((w ↑) •_) (↑-^ w (₁₊ k))

ω^↑≈ω^ : (k : ℕ) → (((ω {n}) ^ k) ↑) ≈ᶠ ((ω {₁₊ n}) ^ k)
ω^↑≈ω^ {n} k =
  PB.trans (PB.refl' ((₂₊ n) CRel,_===_) (↑-^ (ω {n}) k))
           (PP.^-cong ((ω {n}) ↑) ω k ω↑≈ω)
  where module PP = Presentation.Properties ((₂₊ n) CRel,_===_)
