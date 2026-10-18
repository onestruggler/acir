------------------------------------------------------------------------
-- Presentations of groups
--
-- The ctrl lemma for the rules, given completeness on at most eight
-- wires, in the calculus with the schema.
--
-- Every rule of NaturalP, the swap rules included, is an equation
-- between closed words on its own wires, with idle wires on top.  ctrl
-- and ctrl₁ commute with those idle wires (CtrlPad), so the controlled
-- instance is the controlled closed equation, widened: on at most six
-- wires for ctrl₁ and on five for ctrl, which completeness proves since
-- the two sides have the same matrix (CtrlSame), and Schema.widen
-- carries to every width.  A schema instance under ctrl is again an
-- instance; under ctrl₁ it is one, one wire up, conjugated by the swap
-- (Spare.spare-w).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.CtrlBounded
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (T)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit.Base using (tt)
open import Word.Base using (ε)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁ ; ctrl-pad ; ctrl₁-pad ; ctrl-↑)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSame using (soundᴾ ; ctrl-same ; ctrl₁-same)
open import Examples.Groups.CCX+HH.NaturalP.Spare complete≤ using (spare-w)

private
  variable
    n m b : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

------------------------------------------------------------------------
-- A closed core, controlled and widened

-- ctrl, the core on four wires.
core : ∀ {u₀ v₀ : P.Circuit 4} → 4 P.Prop, u₀ === v₀ → ∀ n →
  suc (₄₊ n) S.⊢ ctrl (u₀ P.↓ᵏ n) ≈ ctrl (v₀ P.↓ᵏ n)
core {u₀} {v₀} x n =
  Eq.subst₂ (λ a b → _ S.⊢ a ≈ b) (Eq.sym (ctrl-pad u₀ n)) (Eq.sym (ctrl-pad v₀ n))
    (S.widen n (complete≤ (le 5 tt) (ctrl-same u₀ v₀ (soundᴾ (PB.axiom (P.srel x))))))

-- ctrl₁, the core on its own b wires.
core₁ : ∀ {u₀ v₀ : P.Circuit b} → b P.Prop, u₀ === v₀ → ₂₊ b ≤ 8 → ∀ j →
  (₂₊ b + j) S.⊢ ctrl₁ (u₀ P.↓ᵏ j) ≈ ctrl₁ (v₀ P.↓ᵏ j)
core₁ {u₀ = u₀} {v₀} x b≤ j =
  Eq.subst₂ (λ a b → _ S.⊢ a ≈ b) (Eq.sym (ctrl₁-pad u₀ j)) (Eq.sym (ctrl₁-pad v₀ j))
    (S.widen j (complete≤ b≤ (ctrl₁-same u₀ v₀ (soundᴾ (PB.axiom (P.srel x))))))

------------------------------------------------------------------------
-- Every rule

-- On four or more wires, under ctrl.
bounded-ctrl : ∀ {u v : P.Circuit (₄₊ n)} → (₄₊ n) S.Prop, u === v →
  suc (₄₊ n) S.⊢ ctrl u ≈ ctrl v
bounded-ctrl {n} (S.σrel P.σ-inv) = core (P.σrel P.σ-inv) n
bounded-ctrl {n} (S.σrel (P.σ-nat₁ h)) = core (P.σrel (P.σ-nat₁ h)) n
bounded-ctrl {n} (S.σrel (P.σ-nat₂ h)) = core (P.σrel (P.σ-nat₂ h)) n
bounded-ctrl {n} (S.σrel (P.σ-nat₃ h)) = core (P.σrel (P.σ-nat₃ h)) n
bounded-ctrl {n} (S.srel (S.np P.X²)) = core (P.srel P.X²) n
bounded-ctrl {n} (S.srel (S.np P.CX²)) = core (P.srel P.CX²) n
bounded-ctrl {n} (S.srel (S.np P.CCX²)) = core (P.srel P.CCX²) n
bounded-ctrl {n} (S.srel (S.np P.HH²)) = core (P.srel P.HH²) n
bounded-ctrl {n} (S.srel (S.np P.sw-def)) = core (P.srel P.sw-def) n
bounded-ctrl {n} (S.srel (S.np P.X-control)) = core (P.srel P.X-control) n
bounded-ctrl {n} (S.srel (S.np P.X-controlᵣ)) = core (P.srel P.X-controlᵣ) n
bounded-ctrl {n} (S.srel (S.np P.CNOT-S3)) = core (P.srel P.CNOT-S3) n
bounded-ctrl {n} (S.srel (S.np P.X-Z)) = core (P.srel P.X-Z) n
bounded-ctrl {n} (S.srel (S.np P.CCX-sym)) = core (P.srel P.CCX-sym) n
bounded-ctrl {n} (S.srel (S.np P.CCX-neg)) = core (P.srel P.CCX-neg) n
bounded-ctrl {n} (S.srel (S.np P.CCX-XC)) = core (P.srel P.CCX-XC) n
bounded-ctrl {n} (S.srel (S.np P.HH-swap₀)) = core (P.srel P.HH-swap₀) n
bounded-ctrl {n} (S.srel (S.np P.HH-swap₁)) = core (P.srel P.HH-swap₁) n
bounded-ctrl {n} (S.srel (S.np P.CCX-HH)) = core (P.srel P.CCX-HH) n
bounded-ctrl {n} (S.srel (S.np P.CCX-comm)) = core (P.srel P.CCX-comm) n
-- The schema is closed under ctrl.
bounded-ctrl (S.srel (S.sch s)) = PB.axiom (S.srel (S.srel (S.sch (S.ctl s))))

-- On any number of wires, under ctrl₁.
bounded-ctrl₁ : ∀ {u v : P.Circuit m} → m S.Prop, u === v →
  (₂₊ m) S.⊢ ctrl₁ u ≈ ctrl₁ v
bounded-ctrl₁ (S.σrel (P.σ-inv {k})) = core₁ {b = 2} (P.σrel (P.σ-inv {0})) (le 4 tt) k
bounded-ctrl₁ (S.σrel (P.σ-nat₁ {k} h)) = core₁ {b = 2} (P.σrel (P.σ-nat₁ {0} h)) (le 4 tt) k
bounded-ctrl₁ (S.σrel (P.σ-nat₂ {k} h)) = core₁ {b = 3} (P.σrel (P.σ-nat₂ {0} h)) (le 5 tt) k
bounded-ctrl₁ (S.σrel (P.σ-nat₃ {k} h)) = core₁ {b = 4} (P.σrel (P.σ-nat₃ {0} h)) (le 6 tt) k
bounded-ctrl₁ (S.srel (S.np (P.X² {k}))) = core₁ {b = 1} (P.srel (P.X² {0})) (le 3 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CX² {k}))) = core₁ {b = 2} (P.srel (P.CX² {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CCX² {k}))) = core₁ {b = 3} (P.srel (P.CCX² {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.HH² {k}))) = core₁ {b = 2} (P.srel (P.HH² {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.sw-def {k}))) = core₁ {b = 2} (P.srel (P.sw-def {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.X-control {k}))) = core₁ {b = 2} (P.srel (P.X-control {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.X-controlᵣ {k}))) = core₁ {b = 2} (P.srel (P.X-controlᵣ {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CNOT-S3 {k}))) = core₁ {b = 2} (P.srel (P.CNOT-S3 {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.X-Z {k}))) = core₁ {b = 2} (P.srel (P.X-Z {0})) (le 4 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CCX-sym {k}))) = core₁ {b = 3} (P.srel (P.CCX-sym {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CCX-neg {k}))) = core₁ {b = 3} (P.srel (P.CCX-neg {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CCX-XC {k}))) = core₁ {b = 3} (P.srel (P.CCX-XC {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.HH-swap₀ {k}))) = core₁ {b = 3} (P.srel (P.HH-swap₀ {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.HH-swap₁ {k}))) = core₁ {b = 3} (P.srel (P.HH-swap₁ {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CCX-HH {k}))) = core₁ {b = 3} (P.srel (P.CCX-HH {0})) (le 5 tt) k
bounded-ctrl₁ (S.srel (S.np (P.CCX-comm {k}))) = core₁ {b = 4} (P.srel (P.CCX-comm {0})) (le 6 tt) k
-- … and under ctrl₁, which is ctrl one wire up conjugated by the swap.
bounded-ctrl₁ (S.srel (S.sch {w = w} s)) =
  PB.trans (PB.sym (spare-w w))
  (PB.trans (PB.cong PB.refl
     (PB.cong (S.lemma-cong↑ (ctrl w) ε (PB.axiom (S.srel (S.srel (S.sch (S.ctl s)))))) PB.refl))
  (PB.trans (PB.cong PB.refl PB.left-unit) (PB.axiom (S.srel (S.σrel S.σ-inv)))))

