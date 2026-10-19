------------------------------------------------------------------------
-- Presentations of groups
--
-- The syntax of CNOT-dihedral circuits (Amy, Chen and Ross, "A finite
-- presentation of CNOT-dihedral operators", QPL 2017, EPTCS 266,
-- arXiv:1701.00140): the generators ω, X, T, CNOT of Definition 3.1,
-- the derived gates U and V of Definition 3.2, the relations R₁ … R₁₃
-- of Figure 1, and the structural rules of Section 2
--
-- The paper presents a symmetric monoidal groupoid: circuits compose in
-- sequence and in parallel, and the symmetry (the SWAP gates) is part
-- of the structure — a PROP.  Circuit.Base supplies the PRO:
-- sequential composition, wire shifting and the bifunctorial law
-- (comm₁/comm₂), together with the spatial law for the scalar ω: it is
-- the same on every wire (ω↑=ω), and hence central (comm₀, a theorem
-- of these rules).  Circuit.Prop supplies the symmetry, with SWAP the
-- designated swap: it is an involution (σ-inv) and natural in every
-- generator (σ-nat₁ for X and T, σ-nat₂ for CNOT and for SWAP itself,
-- which is the braid relation; ω by comm₀).  These are the rules the
-- paper assumes before its thirteen, in the shape Lafont's
-- presentations give them; swap-order, swap-braid, swap-X, swap-T and
-- swap-CNOT below state them as the paper's figures draw them.
--
-- Wires are numbered from the bottom: wire 0 is the paper's lowest
-- wire.  A two-wire gate sits on wires 0 and 1; CNOT's control is wire
-- 1 and its target wire 0, as in the paper's diagrams, where the
-- control is the upper wire.  A gate on non-adjacent wires is, as in
-- the paper (Section 3), the gate on adjacent wires conjugated by
-- SWAPs.  The paper draws one instance; the four-wire instances of R₉
-- and R₁₃ follow the same rule.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Presentation.GroupLike using (Grouplike)

import Circuit.Prop
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.PropositionalEquality as Eq

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates

-- The scalar ω = e^{iπ/4} is a gate on no wires.
data Gate : ℕ → Set where
  ω-gate               : Gate 0
  X-gate T-gate        : Gate 1
  CNOT-gate SWAP-gate  : Gate 2

private module SC = Circuit.Prop Gate SWAP-gate

open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_
        ; _Sym,_===_ ; σ-inv ; σ-nat₁ ; σ-nat₂ ; σ-nat₃ )

pattern ω-gen    = gate₀ ω-gate
pattern X-gen    = gate₁ X-gate
pattern T-gen    = gate₁ T-gate
pattern CNOT-gen = gate₂ CNOT-gate
pattern SWAP-gen = gate₂ SWAP-gate

-- The generators as one-letter circuits.
ω : Circuit n
ω = [ ω-gen ]ʷ

X T : Circuit (₁₊ n)
X = [ X-gen ]ʷ
T = [ T-gen ]ʷ

CNOT SWAP : Circuit (₂₊ n)
CNOT = [ CNOT-gen ]ʷ
SWAP = [ SWAP-gen ]ʷ

------------------------------------------------------------------------
-- Derived gates (Definition 3.2)
--
-- U = CNOT · T · CNOT with T on the target: the phase ω^(x₀ ⊕ x₁).
-- V = CNOT₂₁ · CNOT₁₀ · T₀ · CNOT₁₀ · CNOT₂₁: the phase ω^(x₀ ⊕ x₁ ⊕ x₂).

U : Circuit (₂₊ n)
U = CNOT • T • CNOT

V : Circuit (₃₊ n)
V = CNOT ↑ • CNOT • T • CNOT • CNOT ↑

------------------------------------------------------------------------
-- Gates on non-adjacent wires
--
-- Conjugated by the swaps that bring their wires together.  Subscripts
-- list the wires the gate acts on, from the bottom.

-- CNOT with control wire 2 and target wire 0 (the left side of R₆).
CNOT₂₀ : Circuit (₃₊ n)
CNOT₂₀ = SWAP • CNOT ↑ • SWAP

U₀₂ : Circuit (₃₊ n)
U₀₂ = SWAP • U ↑ • SWAP

U₁₃ U₀₃ : Circuit (₄₊ n)
U₁₃ = SWAP ↑ • U ↑ ↑ • SWAP ↑
U₀₃ = SWAP • SWAP ↑ • U ↑ ↑ • SWAP ↑ • SWAP

V₀₂₃ V₀₁₃ : Circuit (₄₊ n)
V₀₂₃ = SWAP • V ↑ • SWAP
V₀₁₃ = SWAP ↑ • SWAP • V ↑ • SWAP • SWAP ↑

------------------------------------------------------------------------
-- The relations (Figure 1)
--
-- Each is stated at the width it is drawn on; the structural rules lift
-- it to every width.  A block fⁿ is the word power f ^ n.  The laws of
-- the symmetry are not here: they are Circuit.Prop's.

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- Affine relations.
  R₁  : (₁₊ n) SRel, X • X === ε
  R₂  : (₂₊ n) SRel, CNOT • X • CNOT === X
  R₃  : (₂₊ n) SRel, CNOT • X ↑ • CNOT === X ↑ • X
  R₄  : (₂₊ n) SRel, CNOT • CNOT === ε
  R₅  : (₂₊ n) SRel, SWAP === CNOT • SWAP • CNOT • SWAP • CNOT
  R₆  : (₃₊ n) SRel, CNOT₂₀ === CNOT • CNOT ↑ • CNOT • CNOT ↑

  -- Diagonal relations.
  R₇  : (₁₊ n) SRel, T ^ 8 === ε
  R₈  : (₂₊ n) SRel, U ^ 4 === T ^ 4 • (T ↑) ^ 4
  R₉  : (₃₊ n) SRel,
        V ^ 2 === T ^ 6 • (T ↑) ^ 6 • (T ↑ ↑) ^ 6 • (U ↑) ^ 2 • U₀₂ ^ 2 • U ^ 2
  R₁₀ : n SRel, ω ^ 8 === ε

  -- Commutation relations.
  R₁₁ : (₁₊ n) SRel, X • T • X === ω • T ^ 7
  R₁₂ : (₂₊ n) SRel, CNOT • T ↑ • CNOT === T ↑
  R₁₃ : (₄₊ n) SRel,
        CNOT ↑ ↑ • V • CNOT ↑ ↑ ===
        T ^ 5 • (T ↑) ^ 5 • (T ↑ ↑) ^ 5 • (T ↑ ↑ ↑) ^ 5 •
        (U ↑ ↑) ^ 3 • U₁₃ ^ 3 • U₀₃ ^ 3 • (U ↑) ^ 3 • U₀₂ ^ 3 • U ^ 3 •
        V ↑ • V₀₂₃ • V₀₁₃ • V

------------------------------------------------------------------------
-- The full relation: the laws of the symmetry (Circuit.Prop) and the
-- structural rules (Circuit.Base) on top
--
-- An instance r of Figure 1 is srel (srel r); one s of the laws of
-- the symmetry is srel (σrel s) — srel (σrel σ-inv), srel (σrel (σ-nat₁
-- X-gate)), and so on — and sym-rule s as an equation.  Agda tells
-- the two srels apart by type.

private module LP = SC.Lift-To-Prop _SRel,_===_

open LP public
  using ( _Prop,_===_ ; σrel ; sym-rule
        ; srel ; cong↑ ; comm₁ ; comm₂ ; comm₃ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₁-w↑ ; comm-gate₂-w↑↑ ; _VRel,_===_ )

-- The scalar is central: not a rule but a theorem of the others
-- (Circuit.Base), there being a single scalar.
open LP.Single-Scalar (λ { ω-gate ω-gate → Eq.refl }) public using (comm₀ ; comm-gate₀-w)

-- The monoid congruence generated by the relations at width n: the
-- paper's equality of circuits.
infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (n VRel,_===_) w v

------------------------------------------------------------------------
-- The laws of the symmetry, as the paper draws them (Section 2)
--
-- Circuit.Prop's rules at SWAP: an involution, coherent (the braid
-- relation, σ-nat₂ at SWAP), and natural with respect to the one- and
-- two-wire generators.  Naturality moves a gate up one wire (or, for
-- CNOT, the pair of wires it sits on up by one) through the swaps that
-- carry those wires.

swap-order : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
swap-order = LP.σ-invol

swap-braid : (₃₊ n) ⊢ SWAP • SWAP ↑ • SWAP ≈ SWAP ↑ • SWAP • SWAP ↑
swap-braid = LP.yang-baxter

swap-X : (₂₊ n) ⊢ X • SWAP ≈ SWAP • X ↑
swap-X = sym-rule (σ-nat₁ X-gate)

swap-T : (₂₊ n) ⊢ T • SWAP ≈ SWAP • T ↑
swap-T = sym-rule (σ-nat₁ T-gate)

swap-CNOT : (₃₊ n) ⊢ CNOT • SWAP ↑ • SWAP ≈ SWAP ↑ • SWAP • CNOT ↑
swap-CNOT = PB.trans (sym-rule (σ-nat₂ CNOT-gate)) PB.assoc

------------------------------------------------------------------------
-- Every generator is invertible, so the presented monoid is a group

grouplike : Grouplike (_VRel,_===_ n)
grouplike {n} ω-gen =
  ω ^ 7 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel (srel R₁₀)))
grouplike X-gen    = X     , PB.axiom (srel (srel R₁))
grouplike {n} T-gen =
  T ^ 7 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel (srel R₇)))
grouplike CNOT-gen = CNOT  , PB.axiom (srel (srel R₄))
grouplike SWAP-gen = SWAP  , swap-order
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
