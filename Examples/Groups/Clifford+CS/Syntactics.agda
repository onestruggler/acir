------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford+CS circuits: the gate set, the shortcuts, and the rules
--
-- This is the syntactic side of a Clifford+CS analogue of
--
--   A. Clément, "A Complete Equational Theory for Real-Clifford+CH
--   Quantum Circuits", arXiv:2602.06644,
--
-- whose formalisation is Real-Clifford+CH: circuits are related to
-- words in the one- and two-level matrices, whose complete equational
-- theory is known — here the one of Bian and Selinger, "Generators and
-- relations for Uₙ(ℤ[½,i])", proved in Clifford+CS-TwoLevel — by an
-- encoding and a decoding, and the circuit rules are what it takes to
-- carry the two-level relations back to circuits.
--
-- The gates are those of Bian and Selinger, "Generators and relations
-- for 3-qubit Clifford+CS operators" (arXiv:2306.08530), formalised in
-- Clifford+CS-3qubit:
--
--   * the scalar i, a 0-ary gate (iI);
--   * S = diag(1, i) and K = γ⁻¹ [[1, 1], [1, −1]] on one wire, where
--     γ = 1 + i, so that K = ω† H;
--   * the controlled phase CS = diag(1, 1, 1, i) on two wires.
--
-- Every gate matrix has entries in ℤ[½,i], and so does every circuit.
-- They are read as wire-indexed words over Circuit.Base: wire 0 is the
-- first tensor factor, the most significant bit of a basis index (as in
-- Bian and Selinger, whose S₀ is i₄ i₅ i₆ i₇ on three qubits), and a
-- two-wire gate sits on wires 0 and 1.
--
-- The rules are Figure 2 of the 3-qubit paper, which is complete for
-- three qubits, stated once each at the width it is drawn on and lifted
-- by Lift-Relation; the commutations of gates on disjoint wires and the
-- centrality of iI are the structural rules, so they are not repeated.
-- On four qubits those rules are not complete (Parity): the number of
-- CS gates mod 2 is invariant under them, and the true equation
-- cx-ccz — a CNOT carries a CCZ on its target to the product of two
-- CCZs — breaks it.  There are three rules on four wires: cx-ccz and its
-- Toffoli analogue toff-ccz, both instances of the substitution of a
-- permutation gate in a phase polynomial (with them the phase gadget's
-- identities are derivable, scratchpad/lemmas5.py), and ck-tct, a gate
-- controlled white by a wire commuting with one that acts only where the
-- wire is 1 (with it the relations between different gadgets on one pair
-- of basis states, scratchpad/lemmas11.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Syntactics where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Presentation.GroupLike using (Grouplike)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

import Circuit.Base
import Presentation.Base as PB
import Presentation.Properties as PP

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gate type

data Gate : ℕ → Set where
  I-gate  : Gate 0      -- the scalar i
  S-gate  : Gate 1
  K-gate  : Gate 1
  CS-gate : Gate 2

------------------------------------------------------------------------
-- Syntactic framework

private module SC = Circuit.Base Gate

open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_ )

pattern I-gen  = gate₀ I-gate
pattern S-gen  = gate₁ S-gate
pattern K-gen  = gate₁ K-gate
pattern CS-gen = gate₂ CS-gate

-- The four generators as one-letter circuits.  The scalar lives at
-- every width; a one-wire gate sits on wire 0, CS on wires 0 and 1.
iI : Circuit n
iI = [ I-gen ]ʷ

S K : Circuit (₁₊ n)
S = [ S-gen ]ʷ
K = [ K-gen ]ʷ

CS : Circuit (₂₊ n)
CS = [ CS-gen ]ʷ

------------------------------------------------------------------------
-- Shortcuts
--
-- The names follow Bian and Selinger, with the wires as subscripts.

-- The Pauli gates: X = K S² K i, and Z = S².
X Z : Circuit (₁₊ n)
X = K • S • S • K • iI
Z = S • S

-- The CNOT with control wire 0 and target wire 1, and the other way
-- round: K on the target conjugating CS², which is CZ.
CX₀₁ CX₁₀ : Circuit (₂₊ n)
CX₀₁ = K ↑ • CS • CS • K ↑ • iI
CX₁₀ = K • CS • CS • K • iI

-- The swap.
Swap : Circuit (₂₊ n)
Swap = CX₀₁ • CX₁₀ • CX₀₁

-- The same on wires 1 and 2.
CX₁₂ CX₂₁ : Circuit (₃₊ n)
CX₁₂ = CX₀₁ ↑
CX₂₁ = CX₁₀ ↑

-- CS on wires 0 and 2, through the swap of wires 1 and 2, and the doubly
-- controlled Z on wires 0, 1, 2, by Barenco's decomposition with the
-- CNOTs between the controls 0, 1: CS₁₂ CX₀₁ CS₁₂⁻¹ CX₀₁ CS₀₂.
CS₀₂ CCZ : Circuit (₃₊ n)
CS₀₂ = Swap ↑ • CS • Swap ↑
CCZ  = CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁ • CS₀₂

-- The Toffoli with its target on wire 0 and its controls on wires 1, 2,
-- and the CCZ on wires 0, 1, 3.
Toff : Circuit (₃₊ n)
Toff = K • CCZ • K • iI

CCZ₀₁₃ : Circuit (₄₊ n)
CCZ₀₁₃ = Swap ↑ ↑ • CCZ • Swap ↑ ↑

-- K on wire 1 controlled by wire 0 (Bian and Selinger's word).
CK : Circuit (₂₊ n)
CK = CS • K ↑ • CS • K ↑ • CS • S • S • S • iI

------------------------------------------------------------------------
-- Group-specific relations: Figure 2 of Bian and Selinger
--
-- Their relations between generators on disjoint wires, and between iI
-- and anything, are the structural rules of Lift-Relation and its
-- theorem Central-Scalars.comm₀; their relations on wires 1 and 2 are
-- the lifts of those on wires 0 and 1.  What is left is below, each
-- with the name of the relation of Clifford+CS-3qubit.Theorem it is.

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- The scalar: iI⁴ = ε.
  order-I : n SRel, iI • iI • iI • iI === ε

  -- One wire: S⁴ = ε, K² = iI³, (S K)³ = iI³.
  order-S  : (₁₊ n) SRel, S • S • S • S === ε
  order-K  : (₁₊ n) SRel, K • K === iI • iI • iI
  order-SK : (₁₊ n) SRel, S • K • S • K • S • K === iI • iI • iI

  -- Two wires.
  order-CS   : (₂₊ n) SRel, CS • CS • CS • CS === ε
  comm-CS-S₀ : (₂₊ n) SRel, CS • S === S • CS
  comm-CS-S₁ : (₂₊ n) SRel, CS • S ↑ === S ↑ • CS
  X-CS₀      : (₂₊ n) SRel, X • CS === CS • CS • CS • X • S ↑
  X-CS₁      : (₂₊ n) SRel, X ↑ • CS === CS • CS • CS • X ↑ • S
  CS-K₀      : (₂₊ n) SRel, CS • K • CS • K • S === S • K • CS • K • CS
  CS-K₁      : (₂₊ n) SRel, CS • K ↑ • CS • K ↑ • S ↑ === S ↑ • K ↑ • CS • K ↑ • CS

  -- Three wires.
  comm-CS↑-CS : (₃₊ n) SRel, CS ↑ • CS === CS • CS ↑
  rel-266 : (₃₊ n) SRel, CX₁₀ • CX₀₁ • CS ↑ • CX₀₁ • CX₁₀ === CX₁₂ • CX₂₁ • CS • CX₂₁ • CX₁₂
  rel-267 : (₃₊ n) SRel, CX₁₀ • CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CX₁₀
                         === CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CS ↑ • CS ↑
  rel-268 : (₃₊ n) SRel, CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁
                         === CS • CX₂₁ • CS • CS • CS • CX₂₁
  rel-269 : (₃₊ n) SRel, CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS
                         === CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑
  rel-272 : (₃₊ n) SRel, CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑
                         === CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS

  -- Four wires: the CNOT from wire 3 onto wire 2 carries the CCZ on
  -- wires 0, 1, 2 to the product of the CCZs on 0, 1, 2 and on 0, 1, 3 —
  -- the phase polynomial (−1)^{x₀x₁(x₂⊕x₃)}.  Not a consequence of the
  -- rules above (Parity).
  cx-ccz : (₄₊ n) SRel, CX₁₀ ↑ ↑ • CCZ • CX₁₀ ↑ ↑ === CCZ • Swap ↑ ↑ • CCZ • Swap ↑ ↑

  -- Four wires: the Toffoli with its target on wire 0 carries the CCZ on
  -- wires 0, 1, 3 — its target and one of its controls — to the product
  -- with the CCZ on wires 1, 2, 3: the substitution x₀ ↦ x₀ ⊕ x₁x₂ in
  -- (−1)^{x₀x₁x₃}.  Independent of the rules above (Parity); whether it
  -- follows from them with cx-ccz is open.
  toff-ccz : (₄₊ n) SRel, Toff • CCZ₀₁₃ • Toff === CCZ₀₁₃ • CCZ ↑

  -- Four wires: K on wire 1 controlled white by wire 0 commutes with the CS
  -- of wires 0 1 conjugated by the Toffoli onto wire 1 from wires 2 3 —
  -- the one acts where x₀ = 0, the other, i^{x₀(x₁ ⊕ x₂x₃)}, only where
  -- x₀ = 1.  A commutation, so the CS parity does not see it.
  ck-tct : (₄₊ n) SRel, X • CK • X • Toff ↑ • CS • Toff ↑ === Toff ↑ • CS • Toff ↑ • X • CK • X

------------------------------------------------------------------------
-- Full relation via Lift-Relation (adds the structural rules cong↑,
-- comm₁, comm₂ and ω↑=ω)

private module LR = SC.Lift-Relation _SRel,_===_
open LR public
  using ( srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₁-w↑ ; comm-gate₂-w↑↑ ; _VRel,_===_ )

-- There is one scalar, so it is central.
open LR.Single-Scalar (λ { I-gate I-gate → Eq.refl }) public
  using (comm₀ ; comm-gate₀-w)

-- The congruence generated, at each width.
infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (_VRel,_===_ n) w v

------------------------------------------------------------------------
-- Grouplike: S⁻¹ = S³, CS⁻¹ = CS³, iI⁻¹ = iI³, K⁻¹ = K iI

grouplike : Grouplike (_VRel,_===_ n)
grouplike I-gen  = iI • iI • iI , PB.trans (PP.by-assoc _ Eq.refl) (PB.axiom (srel order-I))
grouplike S-gen  = S • S • S , PB.trans (PP.by-assoc _ Eq.refl) (PB.axiom (srel order-S))
grouplike CS-gen = CS • CS • CS , PB.trans (PP.by-assoc _ Eq.refl) (PB.axiom (srel order-CS))
grouplike K-gen  = K • iI ,
  PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (PB.sym (comm₀ I-gate K-gen)))
  (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong (PB.axiom (srel order-K)) PB.refl)
  (PB.trans (PP.by-assoc _ Eq.refl) (PB.axiom (srel order-I))))))
grouplike {₁₊ n} (g ↥) with grouplike {n} g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
