------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger's 2-qubit Clifford+T presentation as circuits
-- (Circuit.Base): the gates ω, H, S, T and CZ, and the relations of
-- Figure 1
--
-- The paper's alphabet has a letter for each gate on each qubit (H₀,
-- H₁, …; Generator).  Here a gate is placed on its wires by the shift
-- _↑ of Circuit.Base, and the paper's relations become one rule each:
-- a one-qubit relation, stated for both qubits in the paper, is stated
-- once on the bottom wire and lifted by cong↑, and the monoidal
-- relations (a) — gates on different qubits commute, ω commutes with
-- everything — are the structural rules.  Qubit 1, the last tensor
-- factor, is wire 0 (the bottom wire), and qubit 0 is wire 1; the
-- two-qubit rules keep the paper's names.  Circuits.Iso shows the two
-- presentations isomorphic on two wires, and Circuits.Presentation
-- carries the main theorem over.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+T-2qubit.Circuits.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊)
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
  H-gate S-gate T-gate : Gate 1
  CZ-gate              : Gate 2

private module SC = Circuit.Base Gate

open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ ; _↓ᵏ_ ; _↧ᵏ_ )

pattern ω-gen  = gate₀ ω-gate
pattern H-gen  = gate₁ H-gate
pattern S-gen  = gate₁ S-gate
pattern T-gen  = gate₁ T-gate
pattern CZ-gen = gate₂ CZ-gate

-- The generators as one-letter circuits.
ω : Circuit n
ω = [ ω-gen ]ʷ

H S T : Circuit (₁₊ n)
H = [ H-gen ]ʷ
S = [ S-gen ]ʷ
T = [ T-gen ]ʷ

CZ : Circuit (₂₊ n)
CZ = [ CZ-gen ]ʷ

------------------------------------------------------------------------
-- Derived gates

ω† : Circuit n
ω† = ω ^ 7

X S† T† : Circuit (₁₊ n)
X  = H • S • S • H
S† = S ^ 3
T† = T ^ 7

-- The CNOT and the controlled H with their target on wire 0 (the
-- paper's CX₁, CH₁) and on wire 1 (CX₀, CH₀).
CX CX↓ CH CH↓ : Circuit (₂₊ n)
CX  = H • CZ • H
CX↓ = H ↑ • CZ • H ↑
CH  = S • H • T • CX • T† • H • S†
CH↓ = S ↑ • H ↑ • T ↑ • CX↓ • T† ↑ • H ↑ • S† ↑

------------------------------------------------------------------------
-- The relations (Figure 1, (b)–(e))
--
-- Each is stated at the width it is drawn on; the structural rules lift
-- it to every width.

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- (b) Order of Clifford group elements.
  order-ω  : n SRel, ω ^ 8 === ε
  order-H  : (₁₊ n) SRel, H ^ 2 === ε
  order-S  : (₁₊ n) SRel, S ^ 4 === ε
  order-SH : (₁₊ n) SRel, (S • H) ^ 3 === ω
  order-CZ : (₂₊ n) SRel, CZ ^ 2 === ε

  -- (c) Remaining Clifford relations.
  comm-S0-CZ   : (₂₊ n) SRel, S ↑ • CZ === CZ • S ↑
  comm-S1-CZ   : (₂₊ n) SRel, S • CZ === CZ • S
  rel-X0-CZ    : (₂₊ n) SRel, X ↑ • CZ === CZ • S • S • X ↑
  rel-X1-CZ    : (₂₊ n) SRel, X • CZ === CZ • S ↑ • S ↑ • X
  rel-CZ-H0-CZ : (₂₊ n) SRel,
                 CZ • H ↑ • CZ === S ↑ • H ↑ • CZ • S ↑ • H ↑ • S ↑ • S • ω†
  rel-CZ-H1-CZ : (₂₊ n) SRel,
                 CZ • H • CZ === S • H • CZ • S • H • S • S ↑ • ω†

  -- (d) "Obvious" relations involving T.
  square-T   : (₁₊ n) SRel, T ^ 2 === S
  order-TX   : (₁₊ n) SRel, (T • X) ^ 2 === ω
  comm-T0-CZ : (₂₊ n) SRel, T ↑ • CZ === CZ • T ↑
  swap-T0    : (₂₊ n) SRel,
               H • CZ • H ↑ • H • CZ • H ↑ • T ↑ === T • H • CZ • H ↑ • H • CZ • H ↑

  -- (e) "Non-obvious" relations involving T.
  rel-A : (₂₊ n) SRel,
          CX • T • H • T† • CX • X • T • H • T† ===
          T • H • T† • CX • X • T • H • T† • CX
  rel-B : (₂₊ n) SRel,
          CX • T • H • T • H • T† • CX • X • T • H • T† • H • T† ===
          T • H • T • H • T† • CX • X • T • H • T† • H • T† • CX
  rel-C : (₂₊ n) SRel,
          CH • H • T • CH • CH↓ • H ↑ • T ↑ • CH↓ ===
          CH↓ • H ↑ • T ↑ • CH↓ • CH • H • T • CH

------------------------------------------------------------------------
-- The full relation: the structural rules of Circuit.Base on top

private module LR = SC.Lift-Relation _SRel,_===_

open LR public
  using ( srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₁-w↑ ; comm-gate₂-w↑↑ ; _VRel,_===_ )

-- The scalar is central: a theorem of the structural rules (Circuit.
-- Base), there being a single scalar.
open LR.Single-Scalar (λ { ω-gate ω-gate → Eq.refl }) public using (comm₀ ; comm-gate₀-w)

-- The monoid congruence generated by the relations at width n.
infix 4 _⊢_≈_
_⊢_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ w ≈ v = PB._≈_ (n VRel,_===_) w v

------------------------------------------------------------------------
-- Every generator is invertible, so the presented monoid is a group

private
  -- T⁸ = (T²)⁴ = S⁴ = ε.
  T⁸ : (₁₊ n) ⊢ T ^ 7 • T ≈ ε
  T⁸ {n} =
    PB.trans (PP.by-assoc ((₁₊ n) VRel,_===_) Eq.refl)
    (PB.trans (PB.cong t² (PB.cong t² (PB.cong t² t²))) (PB.axiom (srel order-S)))
    where
    t² : (₁₊ n) ⊢ T • T ≈ S
    t² = PB.axiom (srel square-T)

grouplike : Grouplike (_VRel,_===_ n)
grouplike {n} ω-gen = ω ^ 7 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel order-ω))
grouplike {n} S-gen = S ^ 3 , PB.trans (PP.by-assoc (n VRel,_===_) Eq.refl) (PB.axiom (srel order-S))
grouplike T-gen     = T ^ 7 , T⁸
grouplike H-gen     = H , PB.axiom (srel order-H)
grouplike CZ-gen    = CZ , PB.axiom (srel order-CZ)
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf
