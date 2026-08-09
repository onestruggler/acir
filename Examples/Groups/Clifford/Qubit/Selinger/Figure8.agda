------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's presentation of the n-qubit Clifford operators
-- (arXiv:1310.6813, Figure 8), formalised in our Circuit framework.
--
-- Generators (ExactGate): the scalar ω (∈ Gate 0), H and S (∈ Gate 1),
-- and CZ (∈ Gate 2).  The Pauli operators remain the derived words
-- X = HSSH and Z = SS.
--
-- Relations C1–C15 (Figure 8):
--   (a) n ≥ 0 : ω⁸ = 1                                          (C1)
--   (b) n ≥ 1 : H² = 1, S⁴ = 1, SHSHSH = ω                      (C2–C4)
--   (c) n ≥ 2 : CZ² = 1; S commutes with CZ (either wire);      (C5–C7)
--               X-through-CZ picks up a Z (either wire);        (C8, C9)
--               CZ·H·CZ = … · ω⁻¹                               (C10, C11)
--   (d) n ≥ 3 : CZ↑·CZ = CZ·CZ↑, and three more                 (C12–C15)
--
-- The scalar is a generator, as it is in Selinger.  Making it 0-ary is
-- what buys that: a gate occupying no wires is available at EVERY width
-- (gate₀'s index is an unconstrained n), so one ω serves all n, and
-- Circuit.Base's structural rule comm₀ already says that it commutes
-- with every generator.  Centrality therefore costs no axiom here —
-- ω-central below is the structural rule walked across a word — and C1
-- can be stated at width 0 as Selinger states it.
--
-- Only one relation about the scalar has to be added by hand:
--
--   cω↑  the scalar does not depend on the wire it is written on.  A
--        0-ary gate is width-polymorphic, but _↑ still moves it: ω ↑ is
--        the generator (gate₀ ω-gate) ↥, a different term from
--        gate₀ ω-gate at the same width, and the two name the same
--        scalar.
--
-- An earlier version of this module had no 0-ary gates and made ω the
-- derived one-qubit word (SH)³.  Centrality then had to be an axiom
-- (cω), because nothing else made a derived word commute; without it the
-- presentation was too weak — at width 1 the relations were exactly
-- C1–C4, i.e. ⟨S , H ∣ H² , S⁴ , (SH)²⁴⟩, the von Dyck group D(4,2,24),
-- which is infinite (¼ + ½ + ¹⁄₂₄ < 1), whereas C(1) has order 192.  With
-- a central ω of order 8 the width-1 quotient by ⟨ω⟩ is
-- ⟨S , H ∣ H² , S⁴ , (SH)³⟩ ≅ S₄, and 24 · 8 = 192.  That axiom was also
-- larger than it needed to be: quantified over every generator, its
-- shifted instances followed from comm₁ (ω was a word of 1-ary gates on
-- wire 0) and its S instance from the H instance and C2 (a power
-- commutes with its base, so ω commuted with SH for free, and S = SHH).
-- Only the H and CZ instances carried content.  All of it goes away
-- here.  C4, likewise, was an identity there and is a genuine relation
-- here.
--
-- This is the *exact* Clifford group (with the order-8 scalar ω and
-- S⁴ = 1, not the phaseless S² = 1 of the symplectic quotient).  The
-- structural rules (cong↑, comm₀, comm₁, comm₂) come from Lift-Relation.
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

-- Gate types for the exact Clifford group generators.
data ExactGate : ℕ → Set where
  ω-gate  : ExactGate 0
  H-gate  : ExactGate 1
  S-gate  : ExactGate 1
  CZ-gate : ExactGate 2

-- The circuit framework over this gate set: Gen, the shifts, CRel and
-- the structural rules.  Re-exported, since the generators of Figure 8
-- are exactly the generators of this framework.
open import Circuit.Base ExactGate
  using ( Gen ; Circuit ; CRel ; gate₀ ; gate₁ ; gate₂
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; module Lift-Relation) public

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The generators, as one-letter words

-- The scalar.  Being 0-ary it lives at every width, width 0 included.
ω : Word (Gen n)
ω = [ gate₀ ω-gate ]ʷ

S : Word (Gen (₁₊ n))
S = [ gate₁ S-gate ]ʷ

H : Word (Gen (₁₊ n))
H = [ gate₁ H-gate ]ʷ

CZ : Word (Gen (₂₊ n))
CZ = [ gate₂ CZ-gate ]ʷ

------------------------------------------------------------------------
-- Derived words

-- SH, the one-qubit word S·H.
SH : Word (Gen (₁₊ n))
SH = S • H

-- ω has order 8, so ω⁻¹ = ω⁷.
ω⁻¹ : Word (Gen n)
ω⁻¹ = ω ^ 7

-- X = HSSH, Z = SS  (Selinger §4).
X : Word (Gen (₁₊ n))
X = H • S ^ 2 • H

Z : Word (Gen (₁₊ n))
Z = S ^ 2

-- The two-wire words of C13–C15.
ₕ|ₕ : Word (Gen (₂₊ n))
ₕ|ₕ = H ↓ • CZ • H ↓

ʰ|ʰ : Word (Gen (₂₊ n))
ʰ|ʰ = H ↑ • CZ • H ↑

⊥⊤ : Word (Gen (₂₊ n))
⊥⊤ = ₕ|ₕ • ʰ|ʰ

⊤⊥ : Word (Gen (₂₊ n))
⊤⊥ = ʰ|ʰ • ₕ|ₕ

------------------------------------------------------------------------
-- The Figure-8 relations

infix 4 _Sel,_===_

data _Sel,_===_ : (n : ℕ) → CRel n where

  -- (a) n ≥ 0.  The scalar is 0-ary, so this really is every width.
  c1  : ∀ {n} → n Sel,  ω ^ 8 === ε

  -- (b) n ≥ 1
  c2  : ∀ {n} → (₁₊ n) Sel,  H ^ 2 === ε
  c3  : ∀ {n} → (₁₊ n) Sel,  S ^ 4 === ε

  -- C4 names the scalar: the one-qubit word (SH)³ IS ω.  With ω a
  -- generator this is a genuine relation (it was an identity in the
  -- version that defined ω to be (SH)³), and it is the only place the
  -- scalar meets the wire-consuming gates.
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

  -- The scalar does not depend on the wire it is written on.  gate₀ is
  -- width-polymorphic, but _↑ still relabels it, so ω ↑ and ω are
  -- different terms at the same width and have to be identified.
  --
  -- (Centrality needs no axiom: it is Circuit.Base's comm₀.)
  cω↑ : ∀ {n} → (₁₊ n) Sel,  ω ↑ === ω

  -- (d) n ≥ 3
  c12 : ∀ {n} → (₃₊ n) Sel,  CZ ↑ • CZ === CZ • CZ ↑
  c13 : ∀ {n} → (₃₊ n) Sel,  ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑ === ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  c14 : ∀ {n} → (₃₊ n) Sel,  (⊤⊥ ↑ • CZ ↓) ^ 3 === ε
  c15 : ∀ {n} → (₃₊ n) Sel,  (⊥⊤ ↓ • CZ ↑) ^ 3 === ε

------------------------------------------------------------------------
-- The full relation, with the structural rules
-- srel / cong↑ / comm₀ / comm₁ / comm₂.

open Lift-Relation _Sel,_===_ public

infix 4 _CRel,_===_
_CRel,_===_ : (n : ℕ) → CRel n
_CRel,_===_ = _VRel,_===_

infix 4 _≈ᶠ_
_≈ᶠ_ : {n : ℕ} → Word (Gen n) → Word (Gen n) → Set
_≈ᶠ_ {n} = PB._≈_ (n CRel,_===_)

------------------------------------------------------------------------
-- The scalar is central
--
-- comm₀ gives it for the generators, with no axiom of our own; a word
-- commutes with ω because each of its letters does.  (ε and _•_ are the
-- two other cases: the empty word by the unit laws, a concatenation by
-- walking ω across both halves.)

ω-central : (w : Word (Gen n)) → (ω • w) ≈ᶠ (w • ω)
ω-central [ g ]ʷ  = PB.sym (PB.axiom (comm₀ ω-gate g))
ω-central ε       = PB.trans PB.right-unit (PB.sym PB.left-unit)
ω-central (w • v) =
  PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (ω-central w) PB.refl)
      (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl (ω-central v)) (PB.sym PB.assoc))))

-- Hence so does every power of ω: the scalars are a central subgroup.
ω^-central : (k : ℕ) (w : Word (Gen n)) → ((ω ^ k) • w) ≈ᶠ (w • (ω ^ k))
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
  PB.trans (PB.refl' ((₁₊ n) CRel,_===_) (↑-^ (ω {n}) k))
           (PP.^-cong ((ω {n}) ↑) ω k ω↑≈ω)
  where module PP = Presentation.Properties ((₁₊ n) CRel,_===_)
