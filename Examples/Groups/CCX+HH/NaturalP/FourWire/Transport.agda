------------------------------------------------------------------------
-- Presentations of groups
--
-- The Hadamard embedding ψ (FourWire.Embed) carries every derivation
-- of the CCX+H rules on three wires to one of the CCX+HH rules on four,
-- given the four-wire rule R4 = (CCX · HH(0,3))⁴ = CZ: the image of the
-- CCX+H rule CCXH⁴ is R4, and every other rule's image follows from the
-- CCX+HH rules on at most three wires (decided by Fast), the CCX+HH rules
-- one wire up, and the swap calculus.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.CCX+HH.NaturalP.FourWire.Embed using (R4)

module Examples.Groups.CCX+HH.NaturalP.FourWire.Transport (r4 : R4) where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Examples.Groups.CCX+H.NaturalP.Schema as H
import Examples.Groups.CCX+HH.NaturalP.Schema as S
import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.CCX+H.NaturalP.Syntactics as NH
import Examples.Groups.CCX+HH.NaturalP.Syntactics as NP
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Kit using (fast₃)
open import Examples.Groups.CCX+HH.NaturalP.FourWire.Embed using (ψ ; lift ; past)

------------------------------------------------------------------------
-- Tools

private
  -- re-bracketing, for closed words
  ra : (w v : S.Circuit 4) →
       PP.to-list (4 S.VRel,_===_) w ≡ PP.to-list (4 S.VRel,_===_) v → 4 S.⊢ w ≈ v
  ra w v = PP.by-assoc (4 S.VRel,_===_)

------------------------------------------------------------------------
-- Two wires: every axiom instance, by Fast on three

ax₂ : ∀ {u v} → 2 H.VRel, u === v → 3 S.⊢ ψ u ≈ ψ v
ax₂ {u} {v} (H.srel (H.σrel H.σ-inv))              = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.σrel (H.σ-nat₁ H.X-gate)))  = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.σrel (H.σ-nat₁ H.H-gate)))  = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.X²)))         = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.H²)))         = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.XH⁸)))        = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.CX²)))        = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.sw-def)))     = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.X-control)))  = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.X-controlᵣ))) = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.CNOT-S3)))    = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.X-Z)))        = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.srel (H.srel (H.nh NH.CZ-XC)))      = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.cong↑ (H.srel (H.srel (H.nh NH.X²))))  = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.cong↑ (H.srel (H.srel (H.nh NH.H²))))  = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.cong↑ (H.srel (H.srel (H.nh NH.XH⁸)))) = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ (H.cong↑ (H.cong↑ (H.srel (H.σrel ()))))
ax₂ (H.cong↑ (H.cong↑ (H.srel (H.srel (H.nh ())))))
ax₂ (H.cong↑ (H.comm₁ h (H.gate₀ ())))
ax₂ {u} {v} (H.comm₁ H.X-gate (H.gate₁ H.X-gate)) = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.comm₁ H.X-gate (H.gate₁ H.H-gate)) = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.comm₁ H.H-gate (H.gate₁ H.X-gate)) = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ {u} {v} (H.comm₁ H.H-gate (H.gate₁ H.H-gate)) = fast₃ (ψ u) (ψ v) Eq.refl
ax₂ (H.comm₁ h (H.gate₀ ()))
ax₂ (H.comm₁ h (H.gate₀ () H.↥))
ax₂ (H.comm₂ h (H.gate₀ ()))
ax₂ (H.ω↑=ω ())

------------------------------------------------------------------------
-- Facts on four wires

private
  ψHHw₃ : 3 S.⊢ ψ (H.HHw {0}) ≈ S.HH S.↑
  ψHHw₃ = fast₃ _ _ Eq.refl

  -- H on wires 0 and 1 is HH on wires 1 and 2, the partner cancelled.
  ψHHw : 4 S.⊢ ψ (H.HHw {1}) ≈ S.HH S.↑
  ψHHw = S.widen 1 ψHHw₃

  ψXC : 4 S.⊢ ψ (H.XC {1}) ≈ S.XC S.↑
  ψXC = PB.cong ψHHw (PB.cong PB.refl ψHHw)

  -- … and H on wires 1 and 2 is HH on wires 2 and 3.
  ψHHw↑ : 4 S.⊢ ψ (H.HHw {0} H.↑) ≈ S.HH S.↑ S.↑
  ψHHw↑ =
    PB.trans (lift (H.HHw {0}))
    (PB.trans (PB.cong PB.refl (PB.cong (S.lemma-cong↑ _ _ ψHHw₃) PB.refl))
      (past (S.gate₂ S.HH-gate)))

  -- Conjugation by P … Q, with Q • P ≈ ε, keeps a commutation.
  cj : ∀ {P Q A B : S.Circuit 4} → 4 S.⊢ Q • P ≈ ε → 4 S.⊢ A • B ≈ B • A →
       4 S.⊢ (P • A • Q) • (P • B • Q) ≈ (P • B • Q) • (P • A • Q)
  cj {P} {Q} {A} {B} qp ab =
    PB.trans (squeeze A B)
    (PB.trans (PB.cong PB.refl (PB.cong ab PB.refl))
      (PB.sym (squeeze B A)))
    where
    squeeze : ∀ U V → 4 S.⊢ (P • U • Q) • (P • V • Q) ≈ P • (U • V) • Q
    squeeze U V =
      PB.trans PB.assoc
      (PB.cong PB.refl
        (PB.trans PB.assoc
        (PB.trans (PB.cong PB.refl
          (PB.trans (PB.sym PB.assoc)
          (PB.trans (PB.cong qp PB.refl) PB.left-unit)))
        (PB.sym PB.assoc))))

  σσ : 4 S.⊢ S.σ • S.σ ≈ ε
  σσ = S.σ-invol

  -- X one wire up is X conjugated by the swap.
  sX : 4 S.⊢ S.σ • S.X • S.σ ≈ S.X S.↑
  sX =
    PB.trans (PB.cong PB.refl (PB.axiom (S.srel (S.σrel (S.σ-nat₁ S.X-gate)))))
    (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong σσ PB.refl) PB.left-unit))

  -- HH is symmetric.
  sHH : 4 S.⊢ S.σ • S.HH • S.σ ≈ S.HH
  sHH = S.widen 1 (fast₃ (S.σ • S.HH • S.σ) S.HH Eq.refl)

  -- HH on wires 1 and 3, and the swap of wires 2 and 3.
  Y T : S.Circuit 4
  Y = (S.σ • S.HH S.↑ • S.σ) S.↑
  T = S.σ S.↑ S.↑

  TT : 4 S.⊢ T • T ≈ ε
  TT = S.lemma-cong↑ _ _ (S.lemma-cong↑ _ _ S.σ-invol)

  TYT : 4 S.⊢ T • Y • T ≈ S.HH S.↑
  TYT = S.lemma-cong↑ _ _
    (fast₃ (S.σ S.↑ • (S.σ • S.HH S.↑ • S.σ) • S.σ S.↑) S.HH Eq.refl)

  Y≈ : 4 S.⊢ Y ≈ T • S.HH S.↑ • T
  Y≈ = PB.sym
    (PB.trans (PB.cong PB.refl (PB.cong (PB.sym TYT) PB.refl))
    (PB.trans (ra (T • (T • Y • T) • T) ((T • T) • (Y • (T • T))) Eq.refl)
    (PB.trans (PB.cong TT PB.refl)
    (PB.trans PB.left-unit
    (PB.trans (PB.cong PB.refl TT) PB.right-unit)))))

  THH : 4 S.⊢ T • S.HH • T ≈ S.HH
  THH =
    PB.trans (PB.cong PB.refl (PB.sym (PB.axiom (S.comm₂ S.HH-gate (S.gate₂ S.SW-gate)))))
    (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong TT PB.refl) PB.left-unit))

  HH↑HH : 4 S.⊢ S.HH S.↑ • S.HH ≈ S.HH • S.HH S.↑
  HH↑HH = S.widen 1 (fast₃ (S.HH S.↑ • S.HH) (S.HH • S.HH S.↑) Eq.refl)

  YHH : 4 S.⊢ Y • S.HH ≈ S.HH • Y
  YHH =
    PB.trans (PB.cong Y≈ (PB.sym THH))
    (PB.trans (cj TT HH↑HH)
      (PB.cong THH (PB.sym Y≈)))

  -- D = σ[ 2 ], and D⁻ = σ • σ ↑.
  D⁻ D : S.Circuit 4
  D⁻ = S.σ • S.σ S.↑
  D  = S.σ S.↑ • S.σ

  DD⁻ : 4 S.⊢ D • D⁻ ≈ ε
  DD⁻ =
    PB.trans (PB.trans PB.assoc (PB.cong PB.refl
      (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong σσ PB.refl) PB.left-unit))))
    (S.lemma-cong↑ _ _ S.σ-invol)

  D⁻D : 4 S.⊢ D⁻ • D ≈ S.σ • S.σ
  D⁻D =
    PB.trans PB.assoc (PB.cong PB.refl
      (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong (S.lemma-cong↑ _ _ S.σ-invol) PB.refl) PB.left-unit)))

  -- A two-wire gate one wire up, as its conjugate by D.
  nat₂ : (h : S.Gate 2) → 4 S.⊢ D⁻ • [ S.gate₂ h ]ʷ • D ≈ [ S.gate₂ h ]ʷ S.↑
  nat₂ h =
    PB.trans (PB.cong PB.refl (PB.axiom (S.srel (S.σrel (S.σ-nat₂ h)))))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (PB.trans D⁻D σσ) PB.refl) PB.left-unit))

  -- σ • Y • σ is D⁻ • HH ↑ ↑ • D, re-bracketed.
  σYσ : 4 S.⊢ S.σ • Y • S.σ ≈ D⁻ • S.HH S.↑ S.↑ • D
  σYσ = ra _ _ Eq.refl

  c₂ : (h : S.Gate 2) →
       4 S.⊢ (S.σ • Y • S.σ) • [ S.gate₂ h ]ʷ S.↑ ≈ [ S.gate₂ h ]ʷ S.↑ • (S.σ • Y • S.σ)
  c₂ h =
    PB.trans (PB.cong σYσ (PB.sym (nat₂ h)))
    (PB.trans (cj DD⁻ (PB.axiom (S.comm₂ h (S.gate₂ S.HH-gate))))
      (PB.cong (nat₂ h) (PB.sym σYσ)))

------------------------------------------------------------------------
-- Three wires: every axiom instance

ax₃ : ∀ {u v} → 3 H.VRel, u === v → 4 S.⊢ ψ u ≈ ψ v
-- instances on fewer wires, one wire wider
ax₃ (H.srel (H.σrel H.σ-inv)) = S.widen 1 (ax₂ (H.srel (H.σrel H.σ-inv)))
ax₃ (H.srel (H.σrel (H.σ-nat₁ H.X-gate))) = S.widen 1 (ax₂ (H.srel (H.σrel (H.σ-nat₁ H.X-gate))))
ax₃ (H.srel (H.σrel (H.σ-nat₁ H.H-gate))) = S.widen 1 (ax₂ (H.srel (H.σrel (H.σ-nat₁ H.H-gate))))
ax₃ (H.srel (H.srel (H.nh NH.X²)))         = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.X²))))
ax₃ (H.srel (H.srel (H.nh NH.H²)))         = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.H²))))
ax₃ (H.srel (H.srel (H.nh NH.XH⁸)))        = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.XH⁸))))
ax₃ (H.srel (H.srel (H.nh NH.CX²)))        = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.CX²))))
ax₃ (H.srel (H.srel (H.nh NH.sw-def)))     = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.sw-def))))
ax₃ (H.srel (H.srel (H.nh NH.X-control)))  = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.X-control))))
ax₃ (H.srel (H.srel (H.nh NH.X-controlᵣ))) = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.X-controlᵣ))))
ax₃ (H.srel (H.srel (H.nh NH.CNOT-S3)))    = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.CNOT-S3))))
ax₃ (H.srel (H.srel (H.nh NH.X-Z)))        = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.X-Z))))
ax₃ (H.srel (H.srel (H.nh NH.CZ-XC)))      = S.widen 1 (ax₂ (H.srel (H.srel (H.nh NH.CZ-XC))))
-- the swap rules one wire up
ax₃ (H.srel (H.σrel (H.σ-nat₂ H.CX-gate))) =
  S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.σrel (S.σ-nat₂ S.CX-gate))))
ax₃ (H.srel (H.σrel (H.σ-nat₂ H.SW-gate))) =
  S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.σrel (S.σ-nat₂ S.SW-gate))))
-- three-wire rules without H, one wire up
ax₃ (H.srel (H.srel (H.nh NH.CCX²))) =
  S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.CCX²))))
ax₃ (H.srel (H.srel (H.nh NH.CCX-sym))) =
  S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.CCX-sym))))
ax₃ (H.srel (H.srel (H.nh NH.CCX-neg))) =
  S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.CCX-neg))))
-- three-wire rules with HH written H H ↑
ax₃ (H.srel (H.srel (H.nh NH.CCX-XC))) =
  PB.trans (PB.cong PB.refl (PB.cong ψXC (PB.cong PB.refl ψXC)))
    (S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.CCX-XC)))))
ax₃ (H.srel (H.srel (H.nh NH.HH-swap₀))) =
  PB.trans (PB.cong PB.refl (PB.cong ψHHw↑ PB.refl))
  (PB.trans (S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.HH-swap₀)))))
    (PB.sym (PB.cong ψHHw ψHHw↑)))
ax₃ (H.srel (H.srel (H.nh NH.HH-swap₁))) =
  PB.trans (PB.cong PB.refl (PB.cong ψHHw PB.refl))
  (PB.trans (S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.HH-swap₁)))))
    (PB.sym (PB.cong ψHHw ψHHw↑)))
ax₃ (H.srel (H.srel (H.nh NH.CCX-HH))) =
  PB.trans (PB.cong PB.refl (PB.cong ψXC (PB.cong ψHHw ψXC)))
  (PB.trans (S.lemma-cong↑ _ _ (PB.axiom (S.srel (S.srel (S.np NP.CCX-HH)))))
    (PB.sym (PB.cong ψXC (PB.cong ψHHw (PB.cong ψXC PB.refl)))))
-- the controlled (X H)⁴ = −1 is R4
ax₃ (H.srel (H.srel (H.nh NH.CCXH⁴))) = r4
-- one wire up
ax₃ (H.cong↑ {w = u} {v = v} y) =
  PB.trans (lift u)
  (PB.trans (PB.cong PB.refl (PB.cong (S.lemma-cong↑ _ _ (ax₂ y)) PB.refl))
    (PB.sym (lift v)))
-- commutations: a gate other than H, one wire up
ax₃ (H.comm₁ H.X-gate (H.gate₁ H.X-gate)) =
  S.lemma-cong↑ _ _ (PB.axiom (S.comm₁ S.X-gate (S.gate₁ S.X-gate)))
ax₃ (H.comm₁ H.X-gate (H.gate₂ H.CX-gate)) =
  S.lemma-cong↑ _ _ (PB.axiom (S.comm₁ S.X-gate (S.gate₂ S.CX-gate)))
ax₃ (H.comm₁ H.X-gate (H.gate₂ H.SW-gate)) =
  S.lemma-cong↑ _ _ (PB.axiom (S.comm₁ S.X-gate (S.gate₂ S.SW-gate)))
ax₃ (H.comm₁ H.X-gate (H.gate₁ H.X-gate H.↥)) =
  S.lemma-cong↑ _ _ (PB.axiom (S.comm₁ S.X-gate (S.gate₁ S.X-gate S.↥)))
ax₃ (H.comm₁ H.H-gate (H.gate₁ H.X-gate)) = PB.axiom (S.comm₂ S.HH-gate (S.gate₁ S.X-gate))
ax₃ (H.comm₁ H.H-gate (H.gate₂ H.CX-gate)) = PB.axiom (S.comm₂ S.HH-gate (S.gate₂ S.CX-gate))
ax₃ (H.comm₁ H.H-gate (H.gate₂ H.SW-gate)) = PB.axiom (S.comm₂ S.HH-gate (S.gate₂ S.SW-gate))
ax₃ (H.comm₁ H.H-gate (H.gate₁ H.X-gate H.↥)) = PB.axiom (S.comm₂ S.HH-gate (S.gate₁ S.X-gate S.↥))
-- an H on wire 1, on three wires of four
ax₃ (H.comm₁ H.X-gate (H.gate₁ H.H-gate)) = S.widen 1 (ax₂ (H.comm₁ H.X-gate (H.gate₁ H.H-gate)))
ax₃ (H.comm₁ H.H-gate (H.gate₁ H.H-gate)) = S.widen 1 (ax₂ (H.comm₁ H.H-gate (H.gate₁ H.H-gate)))
-- an H on wire 2: HH on wires 0 and 3
ax₃ (H.comm₁ H.X-gate (H.gate₁ H.H-gate H.↥)) =
  PB.trans (PB.cong PB.refl (PB.sym sX))
  (PB.trans (cj σσ (S.comm-gate₁-w↑ S.X-gate (S.σ • S.HH S.↑ • S.σ)))
    (PB.cong sX PB.refl))
ax₃ (H.comm₁ H.H-gate (H.gate₁ H.H-gate H.↥)) =
  PB.trans (PB.cong PB.refl (PB.sym sHH))
  (PB.trans (cj σσ YHH)
    (PB.cong sHH PB.refl))
ax₃ (H.comm₁ h (H.gate₀ ()))
ax₃ (H.comm₁ h (H.gate₀ () H.↥))
ax₃ (H.comm₁ h (H.gate₀ () H.↥ H.↥))
ax₃ (H.comm₂ H.CX-gate (H.gate₁ H.X-gate)) =
  S.lemma-cong↑ _ _ (PB.axiom (S.comm₂ S.CX-gate (S.gate₁ S.X-gate)))
ax₃ (H.comm₂ H.SW-gate (H.gate₁ H.X-gate)) =
  S.lemma-cong↑ _ _ (PB.axiom (S.comm₂ S.SW-gate (S.gate₁ S.X-gate)))
ax₃ (H.comm₂ H.CX-gate (H.gate₁ H.H-gate)) = c₂ S.CX-gate
ax₃ (H.comm₂ H.SW-gate (H.gate₁ H.H-gate)) = c₂ S.SW-gate
ax₃ (H.comm₂ h (H.gate₀ ()))
ax₃ (H.comm₂ h (H.gate₀ () H.↥))
ax₃ (H.comm₃ h (H.gate₀ ()))
ax₃ (H.ω↑=ω ())

------------------------------------------------------------------------
-- Derivations

transport : ∀ {u v} → 3 H.⊢ u ≈ v → 4 S.⊢ ψ u ≈ ψ v
transport PB.refl        = PB.refl
transport (PB.sym p)     = PB.sym (transport p)
transport (PB.trans p q) = PB.trans (transport p) (transport q)
transport (PB.cong p q)  = PB.cong (transport p) (transport q)
transport PB.assoc       = PB.assoc
transport PB.left-unit   = PB.left-unit
transport PB.right-unit  = PB.right-unit
transport (PB.axiom x)   = ax₃ x
