------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger's 3-qubit Clifford+CS presentation as circuits
-- (Circuit.Base): the gates iI, S, K and CS, and the relations of
-- Figure 2
--
-- The paper's alphabet has a letter for each gate on each qubit (S₀,
-- S₁, S₂, CS₀₁, CS₁₂, …; Theorem.CliffordCS).  Here a gate is placed
-- on its wires by the shift _↑ of Circuit.Base, and the paper's
-- relations become one rule each: a relation the paper states for
-- every qubit, or for both pairs of adjacent qubits, is stated once on
-- the bottom wires and lifted by cong↑, and the commutations of gates
-- on disjoint qubits, and of the scalar iI with everything, are the
-- structural rules.  Qubit 2, the last tensor factor, is wire 0 (the
-- bottom wire), qubit 1 wire 1 and qubit 0 wire 2, so CS₁₂ is CS and
-- CS₀₁ is CS ↑.  Circuits.Iso shows the two presentations isomorphic
-- on three wires, and Circuits.Presentation carries the main theorem
-- over.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS-3qubit.Circuits.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
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

-- The scalar i is a gate on no wires; K = ω† H.
data Gate : ℕ → Set where
  iI-gate        : Gate 0
  S-gate K-gate  : Gate 1
  CS-gate        : Gate 2

private module SC = Circuit.Base Gate

open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_ )

pattern iI-gen = gate₀ iI-gate
pattern S-gen  = gate₁ S-gate
pattern K-gen  = gate₁ K-gate
pattern CS-gen = gate₂ CS-gate

-- The generators as one-letter circuits.
iI : Circuit n
iI = [ iI-gen ]ʷ

S K : Circuit (₁₊ n)
S = [ S-gen ]ʷ
K = [ K-gen ]ʷ

CS : Circuit (₂₊ n)
CS = [ CS-gen ]ʷ

------------------------------------------------------------------------
-- Derived gates, as the paper writes them

-- X on wire 0.
X : Circuit (₁₊ n)
X = K • S • S • K • iI

-- The CNOTs between wires 0 and 1 (the paper's CX₁₂, control on wire
-- 1, and CX₂₁), and between wires 1 and 2 (CX₀₁, control on wire 2,
-- and CX₁₀), with the scalar on no wire.
CX CX↓ : Circuit (₂₊ n)
CX  = K • CS • CS • K • iI
CX↓ = K ↑ • CS • CS • K ↑ • iI

CXᵘ CXᵘ↓ : Circuit (₃₊ n)
CXᵘ  = K ↑ • CS ↑ • CS ↑ • K ↑ • iI
CXᵘ↓ = K ↑ ↑ • CS ↑ • CS ↑ • K ↑ ↑ • iI

------------------------------------------------------------------------
-- The relations (Figure 2)
--
-- Each is stated at the width it is drawn on; the structural rules lift
-- it to every width.

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- The scalar.
  order-iI : n SRel, iI ^ 4 === ε

  -- One qubit.
  order-S  : (₁₊ n) SRel, S ^ 4 === ε
  order-K  : (₁₊ n) SRel, K • K === iI ^ 3
  order-SK : (₁₊ n) SRel, S • K • S • K • S • K === iI ^ 3

  -- Two adjacent qubits; the control of CS is either wire.
  order-CS  : (₂₊ n) SRel, CS ^ 4 === ε
  comm-CS-S↑ : (₂₊ n) SRel, CS • S ↑ === S ↑ • CS
  comm-CS-S  : (₂₊ n) SRel, CS • S === S • CS
  X↑-CS     : (₂₊ n) SRel, X ↑ • CS === CS • CS • CS • X ↑ • S
  X-CS      : (₂₊ n) SRel, X • CS === CS • CS • CS • X • S ↑
  CS-K↑     : (₂₊ n) SRel, CS • K ↑ • CS • K ↑ • S ↑ === S ↑ • K ↑ • CS • K ↑ • CS
  CS-K      : (₂₊ n) SRel, CS • K • CS • K • S === S • K • CS • K • CS

  -- Three qubits.
  comm-CS-CS : (₃₊ n) SRel, CS • CS ↑ === CS ↑ • CS
  rel-CX-CS  : (₃₊ n) SRel,
               CXᵘ↓ • CXᵘ • CS • CXᵘ • CXᵘ↓ === CX • CX↓ • CS ↑ • CX↓ • CX
  rel-CX-CS² : (₃₊ n) SRel,
               CXᵘ↓ • CXᵘ • CS • CS • CXᵘ • CXᵘ↓ === CXᵘ • CS • CS • CXᵘ • CS • CS
  rel-CS-CX  : (₃₊ n) SRel,
               CS • CXᵘ • CS • CS • CS • CXᵘ === CS ↑ • CX↓ • CS ↑ • CS ↑ • CS ↑ • CX↓
  rel-CS-K   : (₃₊ n) SRel,
               CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑ ===
               CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS
  rel-CS-K³  : (₃₊ n) SRel,
               CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS ===
               CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑

------------------------------------------------------------------------
-- The full relation: the structural rules of Circuit.Base on top

private module LR = SC.Lift-Relation _SRel,_===_

open LR public
  using ( srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₁-w↑ ; comm-gate₂-w↑↑ ; _VRel,_===_ )

-- The scalar is central: a theorem of the structural rules (Circuit.
-- Base), there being a single scalar.
open LR.Single-Scalar (λ { iI-gate iI-gate → Eq.refl }) public using (comm₀ ; comm-gate₀-w)

-- The monoid congruence generated by the relations at width n.
infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (n VRel,_===_) w v

------------------------------------------------------------------------
-- Every generator is invertible, so the presented monoid is a group

private
  -- (iI • K) • K = iI • iI³ = ε.
  K⁻¹K : (₁₊ n) ⊢ (iI • K) • K ≈ ε
  K⁻¹K {n} =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.axiom (srel order-K)))
    (PB.axiom (srel order-iI)))

grouplike : Grouplike (_VRel,_===_ n)
grouplike {n} iI-gen = iI ^ 3 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel order-iI))
grouplike {n} S-gen  = S ^ 3 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel order-S))
grouplike {n} CS-gen = CS ^ 3 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel order-CS))
grouplike K-gen      = iI • K , K⁻¹K
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
