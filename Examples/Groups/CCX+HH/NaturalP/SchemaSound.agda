------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural rules with the schema are sound at every width.
--
-- A schema instance is the identity: CCX • CCX is, by NaturalP's rule
-- CCX², and ctrl and _↑ preserve that (CtrlSame.ctrl-same, and
-- ShiftSemantics.cong↑ through Bridge.τ-↑).  A derivation is then read
-- in the complete translated calculus of CCX+HH.Presentation, as
-- Natural.Soundness reads a natural one: the rules of NaturalP through
-- Bridge.τ-axiom, a schema instance by completeness there.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.SchemaSound where

open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
open import Function.Base using (_∋_)
open import Notations using (₄₊)
import Presentation.Base as PB

import Examples.Groups.CCX+HH.NaturalP.Syntactics as NP
open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSame using (soundᴾ ; ctrl-same)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; τ-↑ ; τ-axiom ; interpret)
import Examples.Groups.CCX+HH.Natural.Soundness as NS
import Examples.Groups.CCX+HH.Presentation as Tr
import Examples.Groups.CCX+HH.Structural as St
import Examples.Groups.CCX+HH.Semantics as Sem
import Examples.Groups.CCX+HH.GeneralN.ShiftSemantics as Shift

private
  variable
    n k : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- A schema instance is the identity

sch-sem : ∀ {w : Circuit (₄₊ k)} → CtrlCCX k w → interpret w ≡ interpret (Circuit (₄₊ k) ∋ ε)
sch-sem {k = k} base =
  soundᴾ {u = CCX • CCX} {v = ε} (PB.axiom (NP.srel (NP.srel (NP.CCX² {suc k}))))
sch-sem (ctl {w = w} s) = ctrl-same w ε (sch-sem s)
sch-sem (up {w = w} s)  =
  Eq.trans (Eq.cong Sem.interpret (τ-↑ w))
    (Shift.cong↑ {u = τ w} {v = ε} (sch-sem s))

------------------------------------------------------------------------
-- Derivations, in the translated calculus

axiom-Tr : n VRel, w === v → τ w Tr.≈ τ v
axiom-Tr (srel (σrel s))       = NS.natural⇒translated (τ-axiom (NP.srel (NP.σrel s)))
axiom-Tr (srel (srel (np r)))  = NS.natural⇒translated (τ-axiom (NP.srel (NP.srel r)))
axiom-Tr (srel (srel (sch {w = w} s))) = Tr.completeness {u = τ w} {v = ε} (sch-sem s)
axiom-Tr (cong↑ {w = w} {v = v} y) =
  Eq.subst₂ Tr._≈_ (Eq.sym (τ-↑ w)) (Eq.sym (τ-↑ v)) (St.cong↑ (axiom-Tr y))
axiom-Tr (comm₁ h g) = NS.natural⇒translated (τ-axiom (NP.comm₁ h g))
axiom-Tr (comm₂ h g) = NS.natural⇒translated (τ-axiom (NP.comm₂ h g))
axiom-Tr (comm₃ h g) = NS.natural⇒translated (τ-axiom (NP.comm₃ h g))
axiom-Tr (ω↑=ω ())

derivation-Tr : n ⊢ w ≈ v → τ w Tr.≈ τ v
derivation-Tr PB.refl        = PB.refl
derivation-Tr (PB.sym p)     = PB.sym (derivation-Tr p)
derivation-Tr (PB.trans p q) = PB.trans (derivation-Tr p) (derivation-Tr q)
derivation-Tr (PB.cong p q)  = PB.cong (derivation-Tr p) (derivation-Tr q)
derivation-Tr PB.assoc       = PB.assoc
derivation-Tr PB.left-unit   = PB.left-unit
derivation-Tr PB.right-unit  = PB.right-unit
derivation-Tr (PB.axiom x)   = axiom-Tr x

sound : n ⊢ w ≈ v → interpret w ≡ interpret v
sound p = Tr.soundness (derivation-Tr p)
