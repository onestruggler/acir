------------------------------------------------------------------------
-- Presentations of groups
--
-- The syntax of CNOT-dihedral circuits (Amy, Chen and Ross, "A finite
-- presentation of CNOT-dihedral operators", arXiv:1701.00140): the
-- generators ω, X, T, CNOT of Definition 3.1, the derived gates U and V
-- of Definition 3.2, the relations R₁ … R₁₃ of Figure 1, and the
-- structural rules of Section 2
--
-- The paper presents a symmetric monoidal groupoid: circuits compose in
-- sequence and in parallel, and the symmetry (the SWAP gates) is part
-- of the structure.  Circuit.Base supplies sequential composition,
-- wire shifting and the bifunctorial law (comm₁/comm₂), together
-- with the spatial law for the scalar ω (ω↑=ω; that ω is central is
-- then a theorem, Circuit.Base's comm₀).  The symmetry
-- is a generator here, SWAP, with the laws that make a family of gates
-- a coherent natural symmetry spelled out as relations: it is an
-- involution, it satisfies the braid relation (coherence), and it is
-- natural with respect to every generator (X, T, CNOT; ω by the
-- theorem comm₀).
-- These are the rules the paper assumes before its thirteen, and the
-- shape they take here is the one Lafont's presentations use.
--
-- Wires are numbered from the bottom: wire 0 is the paper's lowest
-- wire.  A two-wire gate sits on wires 0 and 1; CNOT's control is wire
-- 1 and its target wire 0, as in the paper's diagrams where the control
-- is the upper wire.  A gate on non-adjacent wires is, as in the paper
-- (Section 3), the gate on the top-most wires conjugated by SWAPs: the
-- swaps move the lower wires up until the gate sits on adjacent wires
-- at the top, and back.  The paper draws one instance; the four-wire
-- instances of R₉ and R₁₃ follow the same rule.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT-Dihedral.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Presentation.GroupLike using (Grouplike)

import Circuit.Base
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

private module SC = Circuit.Base Gate

open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_ )

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
-- U = CNOT · T · CNOT with T on the target: the phase ω^(x₁ ⊕ x₂).
-- V = CNOT₂₁ · CNOT₁₀ · T₀ · CNOT₁₀ · CNOT₂₁: the phase ω^(x₁ ⊕ x₂ ⊕ x₃).

U : Circuit (₂₊ n)
U = CNOT • T • CNOT

V : Circuit (₃₊ n)
V = CNOT ↑ • CNOT • T • CNOT • CNOT ↑

------------------------------------------------------------------------
-- Gates on non-adjacent wires
--
-- Conjugated by the swaps that move their lower wires up to the top.
-- Subscripts list the wires the gate acts on, from the bottom.

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
-- The relations (Figure 1), and the laws of the symmetry
--
-- Each is stated at the width it is drawn on; the structural rules lift
-- it to every width.  A block fⁿ is the word power f ^ n.

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

  -- The symmetry (Section 2): an involution, coherent, and natural
  -- with respect to the one- and two-wire generators.  Naturality
  -- moves a gate up one wire (or, for CNOT, the pair of wires it sits
  -- on up by one) through the swaps that carry those wires.
  swap-order : (₂₊ n) SRel, SWAP • SWAP === ε
  swap-braid : (₃₊ n) SRel, SWAP • SWAP ↑ • SWAP === SWAP ↑ • SWAP • SWAP ↑
  swap-X     : (₂₊ n) SRel, X • SWAP === SWAP • X ↑
  swap-T     : (₂₊ n) SRel, T • SWAP === SWAP • T ↑
  swap-CNOT  : (₃₊ n) SRel, CNOT • SWAP ↑ • SWAP === SWAP ↑ • SWAP • CNOT ↑

------------------------------------------------------------------------
-- The full relation: the structural rules of Circuit.Base on top

private module LR = SC.Lift-Relation _SRel,_===_

open LR public
  using ( srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₁-w↑ ; comm-gate₂-w↑↑ ; _VRel,_===_ )

-- The scalar is central.  Circuit.Base derives this from the other
-- structural rules once scalars commute with one another, which with a
-- single scalar they do by reflexivity.
open LR.Central-Scalars (λ { ω-gate ω-gate → PB.refl }) public
  using (comm₀ ; comm-gate₀-w)

-- The monoid congruence generated by the relations at width n: the
-- paper's equality of circuits.
infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (n VRel,_===_) w v

------------------------------------------------------------------------
-- Every generator is invertible, so the presented monoid is a group

grouplike : Grouplike (_VRel,_===_ n)
grouplike {n} ω-gen =
  ω ^ 7 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel R₁₀))
grouplike X-gen    = X     , PB.axiom (srel R₁)
grouplike {n} T-gen =
  T ^ 7 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel R₇))
grouplike CNOT-gen = CNOT  , PB.axiom (srel R₄)
grouplike SWAP-gen = SWAP  , PB.axiom (srel swap-order)
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
