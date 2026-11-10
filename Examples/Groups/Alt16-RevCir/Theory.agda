------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules (1)–(7) for circuits over X, CX and CCX, restated over this
-- folder's gates, and the half of their equivalence with the
-- translated relations that the semantics gives
--
-- These are the rules r1, …, r7 of
-- Examples.Groups.XCXCCX-4bit.Syntactics (Figure 1 of "Block Normal
-- Forms and Certified Equations for Four-Bit Reversible Circuits"),
-- word for word, with the swap σ of that module the gate Ex here:
-- Ex is the designated swap of Circuit.Prop, so the relation
-- T._VRel,_===_ consists of the seven rules, the laws of the symmetry
-- and the structural rules.
--
-- The second Reidemeister–Schreier step of this folder is between
-- Syntactics' relation (Lafont's relations read on the cycles Ω i, and
-- the six gate rules) and this one, over the same gates, the
-- translations being the identity.  This module has the half that
-- needs no derivation by hand: every rule here holds for functions on
-- states (T-sound), so on four wires it follows from Syntactics'
-- relation, which is complete (t⇒s).  The other half — each of the
-- rules order, near, far, apart and gate-… derived from r1, …, r7 — is
-- not here yet.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Theory where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (refl)
open import Word.Base using (ε ; _•_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Alt16-RevCir.Presentation using (complete)
open import Examples.Groups.Alt16-RevCir.Semantics
  using ( ⟦_⟧ ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; ⨾-cong ; up-cong ; ⟦↑⟧
        ; same-sound ; ax-sound )
open import Examples.Groups.Alt16-RevCir.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates in other positions

-- CX with its control on wire 0 and its target on wire 1.
CX↓ : Circuit (₂₊ n)
CX↓ = Ex • CX • Ex

-- CCX with its controls on wires 2 and 0 and its target on wire 1.
CCX↓ : Circuit (₃₊ n)
CCX↓ = Ex • CCX • Ex

-- CCX with its controls on wires 3 and 2 and its target on wire 0.
CCX₃₂₀ : Circuit (₄₊ n)
CCX₃₂₀ = Ex • CCX ↑ • Ex

------------------------------------------------------------------------
-- The rules

infix 4 _TRel,_===_
data _TRel,_===_ : (n : ℕ) → CRel n where
  r1 : 1 TRel, X • X                       === ε
  r2 : 2 TRel, CX • X ↑ • CX • X ↑         === X
  r3 : 2 TRel, CX • CX↓ • CX               === Ex
  r4 : 3 TRel, CCX • X ↑ ↑ • CCX • X ↑ ↑   === CX
  r5 : 3 TRel, Ex ↑ • CCX • Ex ↑           === CCX
  r6 : 3 TRel, CX↓ • CCX • CX↓             === CCX↓ • CCX • CCX↓
  r7 : 4 TRel, CCX ↑ • CX • CCX ↑          === CCX₃₂₀ • CX

-- With the swap rules and the structural rules.
module T = Lift-To-Prop _TRel,_===_

------------------------------------------------------------------------
-- Soundness for functions on states

private
  trel-sound : ∀ {w v : Circuit n} → n TRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  trel-sound {w = w} {v} r1 = same-sound w v refl
  trel-sound {w = w} {v} r2 = same-sound w v refl
  trel-sound {w = w} {v} r3 = same-sound w v refl
  trel-sound {w = w} {v} r4 = same-sound w v refl
  trel-sound {w = w} {v} r5 = same-sound w v refl
  trel-sound {w = w} {v} r6 = same-sound w v refl
  trel-sound {w = w} {v} r7 = same-sound w v refl

  -- The swap rules and the structural rules are those of Syntactics'
  -- relation, where Semantics has them.
  T-ax-sound : ∀ {w v : Circuit n} → n T.VRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
  T-ax-sound (T.srel (T.srel r)) = trel-sound r
  T-ax-sound (T.srel (T.σrel s)) = ax-sound (srel (σrel s))
  T-ax-sound (T.cong↑ {w = w} {v = v} a) =
    ≐-trans (⟦↑⟧ w) (≐-trans (up-cong (T-ax-sound a)) (≐-sym (⟦↑⟧ v)))
  T-ax-sound (T.comm₁ h x) = ax-sound (comm₁ h x)
  T-ax-sound (T.comm₂ h x) = ax-sound (comm₂ h x)
  T-ax-sound (T.comm₃ h x) = ax-sound (comm₃ h x)
  T-ax-sound (T.ω↑=ω ())

T-sound : ∀ {w v : Circuit n} → n T.⊢ w ≈ v → ⟦ w ⟧ ≐ ⟦ v ⟧
T-sound PB.refl         = ≐-refl
T-sound (PB.sym e)      = ≐-sym (T-sound e)
T-sound (PB.trans e e′) = ≐-trans (T-sound e) (T-sound e′)
T-sound (PB.cong e e′)  = ⨾-cong (T-sound e) (T-sound e′)
T-sound PB.assoc        = ≐-refl
T-sound PB.left-unit    = ≐-refl
T-sound PB.right-unit   = ≐-refl
T-sound (PB.axiom a)    = T-ax-sound a

------------------------------------------------------------------------
-- From the rules to the translated relations, on four wires

-- Every consequence of r1, …, r7 on four wires follows from
-- Syntactics' relation: it is true of functions on states.
t⇒s : ∀ {w v : Circuit 4} → 4 T.⊢ w ≈ v → 4 ⊢ w ≈ v
t⇒s e = complete (T-sound e)
