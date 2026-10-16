------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural rules with the swap as a gate, and a schema: every
-- controlled version of CCX • CCX = ε.
--
-- Rules on boundedly many wires are incomplete from seven wires on
-- (Rules/README.md, the spin double cover): the circuits on n wires
-- lift to Spin(2ⁿ), every bounded rule lifts to +1, and a true
-- equation that lifts to −1 is not derivable.  ctrl lifts to the
-- inclusion of the spin group of the controlled half, which sends −1
-- to −1, and the square of a lifted involution does not depend on the
-- lift; so (ctrl C)² lifts to the same sign as C² one width down.
-- (ctrl CCX)² = C3Xa² lifts to −1 on five wires, so the instances
-- (ctrlʲ⁺¹ CCX)² lift to −1 at every width from five on: they supply
-- what bounded rules cannot.
--
-- An instance is built from CCX • CCX on four wires, with idle wires on
-- top, by ctrl and _↑ (`CtrlCCX`).  So ctrl and ctrl₁ = ctrl ∘ _↑ send
-- an instance to an instance, which is what the ctrl lemma needs, and
-- idle wires on top do too (`pad`), which is what widening needs.
-- Shifted instances are derivable from the others by cong↑, but ctrl of
-- a shifted one would need a lemma moving the spare wire of ctrl₁; they
-- are kept as instances.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Schema where

open import Data.Nat.Base using (ℕ ; suc ; _+_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

import Examples.Groups.CCX+HH.NaturalP.Syntactics as NP
open NP public
  using (Gate ; X-gate ; CX-gate ; HH-gate ; SW-gate ; CCX-gate ;
         X ; CX ; HH ; CCX ; XC ; _NP,_===_)
open import Circuit.Prop Gate SW-gate public
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl-pad)
import Examples.Groups.CCX+HH.NaturalP.Pad as Pad

private
  variable
    n k : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The schema

-- The controlled versions of CCX • CCX, on 4 + k wires.
data CtrlCCX : (k : ℕ) → Circuit (₄₊ k) → Set where
  base : CtrlCCX k (CCX • CCX)
  ctl  : ∀ {w} → CtrlCCX k w → CtrlCCX (suc k) (ctrl w)
  up   : ∀ {w} → CtrlCCX k w → CtrlCCX (suc k) (w ↑)

infix 4 _NPΣ,_===_
data _NPΣ,_===_ : (n : ℕ) → CRel n where
  np  : n NP, w === v → n NPΣ, w === v
  sch : ∀ {w} → CtrlCCX k w → (₄₊ k) NPΣ, w === ε

open Lift-To-Prop _NPΣ,_===_ public

-- Idle wires on top of an instance.
padC : ∀ {w} → CtrlCCX k w → ∀ m → CtrlCCX (k + m) (w ↓ᵏ m)
padC base            m = base
padC (ctl {w = w} s) m = Eq.subst (CtrlCCX _) (ctrl-pad w m) (ctl (padC s m))
padC (up {w = w} s)  m = Eq.subst (CtrlCCX _) (Eq.sym (Pad.↑↓ w m)) (up (padC s m))

------------------------------------------------------------------------
-- NaturalP derivations

emb-ax : n NP.VRel, w === v → n VRel, w === v
emb-ax (NP.srel (NP.σrel s)) = srel (σrel s)
emb-ax (NP.srel (NP.srel r)) = srel (srel (np r))
emb-ax (NP.cong↑ y)          = cong↑ (emb-ax y)
emb-ax (NP.comm₁ h g)        = comm₁ h g
emb-ax (NP.comm₂ h g)        = comm₂ h g
emb-ax (NP.comm₃ h g)        = comm₃ h g
emb-ax (NP.ω↑=ω ())

emb : n NP.⊢ w ≈ v → n ⊢ w ≈ v
emb PB.refl        = PB.refl
emb (PB.sym p)     = PB.sym (emb p)
emb (PB.trans p q) = PB.trans (emb p) (emb q)
emb (PB.cong p q)  = PB.cong (emb p) (emb q)
emb PB.assoc       = PB.assoc
emb PB.left-unit   = PB.left-unit
emb PB.right-unit  = PB.right-unit
emb (PB.axiom x)   = PB.axiom (emb-ax x)

------------------------------------------------------------------------
-- On the bottom wires of any wider circuit

widen-axiom : ∀ {k} (m : ℕ) {w v : Circuit k} → k VRel, w === v →
              (k + m) VRel, w ↓ᵏ m === v ↓ᵏ m
widen-axiom m (srel (σrel s))      = emb-ax (Pad.widen-axiom m (NP.srel (NP.σrel s)))
widen-axiom m (srel (srel (np r))) = emb-ax (Pad.widen-axiom m (NP.srel (NP.srel r)))
widen-axiom m (srel (srel (sch s))) = srel (srel (sch (padC s m)))
widen-axiom m (cong↑ {w = w} {v = v} x) =
  Eq.subst₂ (_VRel,_===_ _) (Eq.sym (Pad.↑↓ w m)) (Eq.sym (Pad.↑↓ v m))
    (cong↑ (widen-axiom m x))
widen-axiom m (comm₁ h g) = comm₁ h (g ↧ᵏ m)
widen-axiom m (comm₂ h g) = comm₂ h (g ↧ᵏ m)
widen-axiom m (comm₃ h g) = comm₃ h (g ↧ᵏ m)
widen-axiom m (ω↑=ω ())

widen : ∀ {k} (m : ℕ) {w v : Circuit k} → k ⊢ w ≈ v → (k + m) ⊢ w ↓ᵏ m ≈ v ↓ᵏ m
widen m PB.refl        = PB.refl
widen m (PB.sym p)     = PB.sym (widen m p)
widen m (PB.trans p q) = PB.trans (widen m p) (widen m q)
widen m (PB.cong p q)  = PB.cong (widen m p) (widen m q)
widen m PB.assoc       = PB.assoc
widen m PB.left-unit   = PB.left-unit
widen m PB.right-unit  = PB.right-unit
widen m (PB.axiom x)   = PB.axiom (widen-axiom m x)
