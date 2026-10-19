------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules on five wires and more
--
-- The rules of Syntactics are complete on four qubits (Four.Complete).
-- From five on they are not expected to be (a rule of the joint paper,
-- AX below, has a parity invariant of the four-wire theory against it),
-- and the rule set for every width adds equations on five wires:
-- AX, the commutation of the doubly controlled S Σ(x; t, y | u, A) with
-- the CS of its two borrowed wires u, A.  They are kept in a relation of
-- their own, the rules of Syntactics included through `old`, so that
-- nothing built on Syntactics changes; `embed` carries a derivation in
-- the old theory to the new one.
--
-- AX at its canonical placement: u = 0, A = 1, t = 3, y = 4, x = 2; the
-- commutator [Toff(1; 3, 4), CS(2, 1)] with the Toffoli onto wire 1,
-- spelled as Five.Letters spells it (scratchpad/five/spell5.py).
--
-- And the controlled versions λ¹ of the four-wire rules lf, hyb-sq and
-- hyb-yb (control wire 4, Five.Lambda.λc): rules on five wires, which
-- the joint paper's tools do not reach (scratchpad/five-qubit-plan.md).
-- The controlled ck-tct is not a rule: it is derived from the rules of
-- Syntactics and AX given completeness on four wires
-- (Five.CKTDerived.ck-tct-derived, the joint paper's de-borrowing over
-- transported two-wire equations, by branch v-office).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Rules where

open import Data.Nat using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
open import Notations using (₄₊)

import Circuit.Base
import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Five.Lambda using (λc)

private
  variable
    n : ℕ
    w v : Word (Gen n)

private module SC = Circuit.Base Gate

------------------------------------------------------------------------
-- AX

module AX where

  -- Toff(1; 3, 4): the Toffoli onto wire 1 from wires 2, 3, its upper
  -- control carried to wire 4 and then its middle one to wire 3.
  T₁₃₄ : Circuit (suc (₄₊ n))
  T₁₃₄ = Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑

  l r : Circuit (suc (₄₊ n))
  l = CS • T₁₃₄ • (CS ↑) • T₁₃₄ • ((CS • CS • CS) ↑)
  r = T₁₃₄ • (CS ↑) • T₁₃₄ • ((CS • CS • CS) ↑) • CS

-- The two sides of ck-tct, named so that its λ-image is stated once
-- (Five.CKTDerived).
module CKT where

  l r : Circuit (₄₊ n)
  l = X • CK • X • Toff ↑ • CS • Toff ↑
  r = Toff ↑ • CS • Toff ↑ • X • CK • X

------------------------------------------------------------------------
-- The relation

infix 4 _XRel,_===_
data _XRel,_===_ : (n : ℕ) → WRel (Gen n) where

  -- The rules of Syntactics.
  old : n SRel, w === v → n XRel, w === v

  -- Five wires.
  ax : (suc (₄₊ n)) XRel, AX.l === AX.r

  -- The controlled four-wire rules.
  λ-lf     : 5 XRel, λc LF.Hyb === λc LF.Dec
  λ-hyb-sq : 5 XRel, λc HSQ.Sq === λc ε
  λ-hyb-yb : 5 XRel, λc HYB.Yl === λc HYB.Yr

private module LX = SC.Lift-Relation _XRel,_===_

open LX public
  using ()
  renaming ( _VRel,_===_ to _XVRel,_===_ ; srel to srelₓ ; cong↑ to cong↑ₓ
           ; comm₁ to comm₁ₓ ; comm₂ to comm₂ₓ ; ω↑=ω to ω↑=ωₓ
           ; lemma-cong↑ to lemma-cong↑ₓ )

-- There is one scalar, so it is central.
open LX.Single-Scalar (λ { I-gate I-gate → Eq.refl }) public
  using () renaming (comm₀ to comm₀ₓ ; comm-gate₀-w to comm-gate₀-wₓ)

-- The congruence generated, at each width.
infix 4 _⊢ₓ_≈_
_⊢ₓ_≈_ : (n : ℕ) → Circuit n → Circuit n → Set
n ⊢ₓ w ≈ v = PB._≈_ (_XVRel,_===_ n) w v

------------------------------------------------------------------------
-- The old theory in the new

embed-ax : n VRel, w === v → n XVRel, w === v
embed-ax (srel a)    = LX.srel (old a)
embed-ax (cong↑ a)   = LX.cong↑ (embed-ax a)
embed-ax (comm₁ h g) = LX.comm₁ h g
embed-ax (comm₂ h g) = LX.comm₂ h g
embed-ax (ω↑=ω h)    = LX.ω↑=ω h

embed : n ⊢ w ≈ v → n ⊢ₓ w ≈ v
embed PB.refl          = PB.refl
embed (PB.sym e)       = PB.sym (embed e)
embed (PB.trans e e₁)  = PB.trans (embed e) (embed e₁)
embed (PB.cong e e₁)   = PB.cong (embed e) (embed e₁)
embed PB.assoc         = PB.assoc
embed PB.left-unit     = PB.left-unit
embed PB.right-unit    = PB.right-unit
embed (PB.axiom a)     = PB.axiom (embed-ax a)
