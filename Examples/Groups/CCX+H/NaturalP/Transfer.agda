------------------------------------------------------------------------
-- Presentations of groups
--
-- From CCX+HH derivations to CCX+H derivations.
--
-- θ (HH ↦ H • H ↑) carries every derivation of CCX+HH.NaturalP with
-- the schema to one of CCX+H.NaturalP with the schema (`θ-cong`).
-- Every rule goes to the rule of the same name, but for HH • HH = ε
-- (H² on each wire, the two H commuting by comm₁), the swap's
-- naturality at HH (`nat₂` at H • H ↑) and HH past a circuit two wires
-- up (comm₁ twice).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Transfer where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₂₊)
import Presentation.Base as PB

import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as PS
open import Examples.Groups.CCX+H.NaturalP.Syntactics as NH
  using (Gate ; X-gate ; H-gate ; CX-gate ; SW-gate ; CCX-gate ; X ; H ; CX ; CCX ; HHw)
open import Examples.Groups.CCX+H.NaturalP.Schema
open import Examples.Groups.CCX+H.NaturalP.Theta using (θg ; θ ; θ-↑)

private
  variable
    n : ℕ

open PB using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

private
  rule : ∀ {w v} → n NH, w === v → n ⊢ w ≈ v
  rule r = axiom (srel (srel (nh r)))

  -- The two H of HH commute.
  H-H↑ : (₂₊ n) ⊢ H ↑ • H ≈ H • H ↑
  H-H↑ = axiom (comm₁ H-gate (gate₁ H-gate))

  HH² : (₂₊ n) ⊢ HHw • HHw ≈ ε
  HH² = trans assoc (trans (cong refl (trans (sym assoc) (cong H-H↑ refl)))
    (trans (cong refl assoc) (trans (sym assoc)
    (trans (cong (rule NH.H²) (lemma-cong↑ _ _ (rule NH.H²))) left-unit))))

  -- HH past a circuit two wires up.
  HH-comm : ∀ (w : Circuit n) → (₂₊ n) ⊢ w ↑ ↑ • HHw ≈ HHw • w ↑ ↑
  HH-comm w = trans (sym assoc) (trans (cong (comm-gate₁-w↑ H-gate (w ↑)) refl)
    (trans assoc (trans (cong refl (lemma-cong↑ _ _ (comm-gate₁-w↑ H-gate w)))
    (sym assoc))))

------------------------------------------------------------------------
-- The transfer

θ-ax : ∀ {w v : P.Circuit n} → n PS.VRel, w === v → n ⊢ θ w ≈ θ v
θ-ax (PS.srel (PS.σrel PS.σ-inv))              = sym-rule σ-inv
θ-ax (PS.srel (PS.σrel (PS.σ-nat₁ PS.X-gate)))   = sym-rule (σ-nat₁ X-gate)
θ-ax (PS.srel (PS.σrel (PS.σ-nat₂ PS.CX-gate)))  = sym-rule (σ-nat₂ CX-gate)
θ-ax (PS.srel (PS.σrel (PS.σ-nat₂ PS.SW-gate)))  = sym-rule (σ-nat₂ SW-gate)
θ-ax (PS.srel (PS.σrel (PS.σ-nat₂ PS.HH-gate)))  = nat₂ (H • H ↑)
θ-ax (PS.srel (PS.σrel (PS.σ-nat₃ PS.CCX-gate))) = sym-rule (σ-nat₃ CCX-gate)
θ-ax (PS.srel (PS.srel (PS.np P.X²)))         = rule NH.X²
θ-ax (PS.srel (PS.srel (PS.np P.CX²)))        = rule NH.CX²
θ-ax (PS.srel (PS.srel (PS.np P.CCX²)))       = rule NH.CCX²
θ-ax (PS.srel (PS.srel (PS.np P.HH²)))        = HH²
θ-ax (PS.srel (PS.srel (PS.np P.sw-def)))     = rule NH.sw-def
θ-ax (PS.srel (PS.srel (PS.np P.X-control)))  = rule NH.X-control
θ-ax (PS.srel (PS.srel (PS.np P.X-controlᵣ))) = rule NH.X-controlᵣ
θ-ax (PS.srel (PS.srel (PS.np P.CNOT-S3)))    = rule NH.CNOT-S3
θ-ax (PS.srel (PS.srel (PS.np P.X-Z)))        = rule NH.X-Z
θ-ax (PS.srel (PS.srel (PS.np P.CCX-sym)))    = rule NH.CCX-sym
θ-ax (PS.srel (PS.srel (PS.np P.CCX-neg)))    = rule NH.CCX-neg
θ-ax (PS.srel (PS.srel (PS.np P.CCX-XC)))     = rule NH.CCX-XC
θ-ax (PS.srel (PS.srel (PS.np P.HH-swap₀)))   = rule NH.HH-swap₀
θ-ax (PS.srel (PS.srel (PS.np P.HH-swap₁)))   = rule NH.HH-swap₁
θ-ax (PS.srel (PS.srel (PS.np P.CCX-HH)))     = rule NH.CCX-HH
θ-ax (PS.srel (PS.srel (PS.np P.CCX-comm)))   = rule NH.CCX-comm
θ-ax (PS.srel (PS.srel (PS.sch c)))           = axiom (srel (srel (sch c)))
θ-ax (PS.cong↑ {w = w} {v = v} x) =
  Eq.subst₂ (_⊢_≈_ _) (Eq.sym (θ-↑ w)) (Eq.sym (θ-↑ v)) (lemma-cong↑ _ _ (θ-ax x))
θ-ax (PS.comm₁ PS.X-gate g)   = comm-gate₁-w↑ X-gate (θg g)
θ-ax (PS.comm₂ PS.CX-gate g)  = comm-gate₂-w↑↑ CX-gate (θg g)
θ-ax (PS.comm₂ PS.SW-gate g)  = comm-gate₂-w↑↑ SW-gate (θg g)
θ-ax (PS.comm₂ PS.HH-gate g)  = HH-comm (θg g)
θ-ax (PS.comm₃ PS.CCX-gate g) = comm-gate₃-w↑↑↑ CCX-gate (θg g)
θ-ax (PS.ω↑=ω ())

θ-cong : ∀ {w v : P.Circuit n} → n PS.⊢ w ≈ v → n ⊢ θ w ≈ θ v
θ-cong PB.refl        = refl
θ-cong (PB.sym p)     = sym (θ-cong p)
θ-cong (PB.trans p q) = trans (θ-cong p) (θ-cong q)
θ-cong (PB.cong p q)  = cong (θ-cong p) (θ-cong q)
θ-cong PB.assoc       = assoc
θ-cong PB.left-unit   = left-unit
θ-cong PB.right-unit  = right-unit
θ-cong (PB.axiom x)   = θ-ax x
