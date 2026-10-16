------------------------------------------------------------------------
-- Presentations of groups
--
-- The ctrl lemma, given completeness on at most eight wires: ctrl and
-- ctrl₁ carry derivations to derivations, in the calculus with the
-- schema (NaturalP.Schema).  Without the schema the hypothesis is false
-- from seven wires on (Rules/README.md).
--
-- A derivation is built from axiom instances by the monoid congruence,
-- which ctrl and ctrl₁ respect on the nose, being homomorphisms.  An
-- axiom instance is a bounded rule or a schema instance (CtrlBounded);
-- a rule one wire up, which under ctrl is the rule under ctrl₁
-- (CtrlPad.ctrl-↑) and under ctrl₁ the rule under ctrl₁ one wire up,
-- conjugated by the swaps of wires 0 1 2 (CtrlPad.ctrl₁-↑); or a
-- commutation (CtrlComm).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.CtrlLemma
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Nat.Base using (suc)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁ ; ctrl-↑ ; ctrl₁-↑)
open import Examples.Groups.CCX+HH.NaturalP.CtrlBounded complete≤
  using (bounded-ctrl ; bounded-ctrl₁)
open import Examples.Groups.CCX+HH.NaturalP.CtrlComm complete≤
  using (pass₁-X ; pass₁-CX ; pass₁-HH ; pass₁-SW ; pass₁-CCX ;
         pass-X ; pass-CX ; pass-HH ; pass-SW ; pass-CCX)

private
  variable
    m : ℕ
    u v : Circuit m

------------------------------------------------------------------------
-- Under ctrl₁, at every width

ctrl₁-axiom : m VRel, u === v → (₂₊ m) ⊢ ctrl₁ u ≈ ctrl₁ v
ctrl₁-axiom (srel x) = bounded-ctrl₁ x
ctrl₁-axiom (cong↑ {w = w} {v = v} y) =
  PB.trans (emb (ctrl₁-↑ w))
  (PB.trans (PB.cong PB.refl
              (PB.cong (lemma-cong↑ (ctrl₁ w) (ctrl₁ v) (ctrl₁-axiom y)) PB.refl))
    (PB.sym (emb (ctrl₁-↑ v))))
ctrl₁-axiom (comm₁ X-gate g)   = pass₁-X g
ctrl₁-axiom (comm₂ CX-gate g)  = pass₁-CX g
ctrl₁-axiom (comm₂ HH-gate g)  = pass₁-HH g
ctrl₁-axiom (comm₂ SW-gate g)  = pass₁-SW g
ctrl₁-axiom (comm₃ CCX-gate g) = pass₁-CCX g
ctrl₁-axiom (ω↑=ω ())

ctrl₁-cong : m ⊢ u ≈ v → (₂₊ m) ⊢ ctrl₁ u ≈ ctrl₁ v
ctrl₁-cong PB.refl         = PB.refl
ctrl₁-cong (PB.sym p)      = PB.sym (ctrl₁-cong p)
ctrl₁-cong (PB.trans p q)  = PB.trans (ctrl₁-cong p) (ctrl₁-cong q)
ctrl₁-cong (PB.cong p q)   = PB.cong (ctrl₁-cong p) (ctrl₁-cong q)
ctrl₁-cong PB.assoc        = PB.assoc
ctrl₁-cong PB.left-unit    = PB.left-unit
ctrl₁-cong PB.right-unit   = PB.right-unit
ctrl₁-cong (PB.axiom x)    = ctrl₁-axiom x

------------------------------------------------------------------------
-- Under ctrl, from four wires on

ctrl-axiom : (₄₊ m) VRel, u === v → suc (₄₊ m) ⊢ ctrl u ≈ ctrl v
ctrl-axiom (srel x) = bounded-ctrl x
ctrl-axiom (cong↑ {w = w} {v = v} y) =
  Eq.subst₂ (λ a b → _ ⊢ a ≈ b) (Eq.sym (ctrl-↑ w)) (Eq.sym (ctrl-↑ v)) (ctrl₁-axiom y)
ctrl-axiom (comm₁ X-gate g)   = pass-X g
ctrl-axiom (comm₂ CX-gate g)  = pass-CX g
ctrl-axiom (comm₂ HH-gate g)  = pass-HH g
ctrl-axiom (comm₂ SW-gate g)  = pass-SW g
ctrl-axiom (comm₃ CCX-gate g) = pass-CCX g
ctrl-axiom (ω↑=ω ())

ctrl-cong : (₄₊ m) ⊢ u ≈ v → suc (₄₊ m) ⊢ ctrl u ≈ ctrl v
ctrl-cong PB.refl         = PB.refl
ctrl-cong (PB.sym p)      = PB.sym (ctrl-cong p)
ctrl-cong (PB.trans p q)  = PB.trans (ctrl-cong p) (ctrl-cong q)
ctrl-cong (PB.cong p q)   = PB.cong (ctrl-cong p) (ctrl-cong q)
ctrl-cong PB.assoc        = PB.assoc
ctrl-cong PB.left-unit    = PB.left-unit
ctrl-cong PB.right-unit   = PB.right-unit
ctrl-cong (PB.axiom x)    = ctrl-axiom x
