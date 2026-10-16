------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport on five wires: every axiom instance of the four-wire theory
--
-- For each instance of Syntactics' rules at every placement on four
-- wires, and of the structural rules, the equation of the λ¹₄-images of
-- its two sides (Five.Transport.AxOk): a window, an F2 item of the joint
-- paper, or an F1 item renamed by a permutation of the domain wires with
-- the borrowed wires put in order by F0; the derivations are the lemmas
-- `lem-tr-…` of Five.D.  What the joint run does not derive is a field
-- of `Missing`: the controlled versions of rel-269, rel-272 and ck-tct
-- (de-borrowing) and of the four-wire rules lf, hyb-sq, hyb-yb (rules on
-- five wires).  Written by `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.TransportAx where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport
open import Examples.Groups.Clifford+CS.Five.D.D230 using (lem-tr-CS-K0-at-0 ; lem-tr-CS-K0-at-1 ; lem-tr-X-CS0-at-0 ; lem-tr-X-CS0-at-1 ; lem-tr-X-CS0-at-2 ; lem-tr-X-CS1-at-0 ; lem-tr-X-CS1-at-1 ; lem-tr-X-CS1-at-2 ; lem-tr-comm-CS-S0-at-0 ; lem-tr-comm-CS-S0-at-1 ; lem-tr-comm-CS-S0-at-2 ; lem-tr-comm-CS-S1-at-0 ; lem-tr-comm-CS-S1-at-1 ; lem-tr-comm-CS-S1-at-2 ; lem-tr-order-CS-at-0 ; lem-tr-order-CS-at-1 ; lem-tr-order-CS-at-2 ; lem-tr-order-I-at-0 ; lem-tr-order-I-at-1 ; lem-tr-order-I-at-2 ; lem-tr-order-I-at-3 ; lem-tr-order-I-at-4 ; lem-tr-order-K-at-0 ; lem-tr-order-K-at-1 ; lem-tr-order-K-at-2 ; lem-tr-order-K-at-3 ; lem-tr-order-S-at-0 ; lem-tr-order-S-at-1 ; lem-tr-order-S-at-2 ; lem-tr-order-S-at-3 ; lem-tr-order-SK-at-0 ; lem-tr-order-SK-at-1 ; lem-tr-order-SK-at-2 ; lem-tr-order-SK-at-3)
open import Examples.Groups.Clifford+CS.Five.D.D231 using (lem-tr-CS-K0-at-2 ; lem-tr-CS-K1-at-0 ; lem-tr-CS-K1-at-1 ; lem-tr-CS-K1-at-2 ; lem-tr-comm-CS-CS-at-0 ; lem-tr-comm-CS-CS-at-1 ; lem-tr-rel-266-at-0 ; lem-tr-rel-266-at-1 ; lem-tr-rel-267-at-0 ; lem-tr-rel-267-at-1 ; lem-tr-rel-268-at-0)
open import Examples.Groups.Clifford+CS.Five.D.D232 using (lem-tr-comm1-K-CS01-at-0 ; lem-tr-comm1-K-CS01-at-1 ; lem-tr-comm1-K-CS12-at-0 ; lem-tr-comm1-K-I-at-0 ; lem-tr-comm1-K-I-at-1 ; lem-tr-comm1-K-I-at-2 ; lem-tr-comm1-K-I-at-3 ; lem-tr-comm1-K-K0-at-0 ; lem-tr-comm1-K-K0-at-1 ; lem-tr-comm1-K-K0-at-2 ; lem-tr-comm1-K-K1-at-0 ; lem-tr-comm1-K-K1-at-1 ; lem-tr-comm1-K-K2-at-0 ; lem-tr-comm1-K-S0-at-0 ; lem-tr-comm1-K-S0-at-1 ; lem-tr-comm1-K-S0-at-2 ; lem-tr-comm1-K-S1-at-0 ; lem-tr-comm1-K-S1-at-1 ; lem-tr-comm1-K-S2-at-0 ; lem-tr-comm1-S-CS01-at-0 ; lem-tr-comm1-S-CS01-at-1 ; lem-tr-comm1-S-CS12-at-0 ; lem-tr-comm1-S-I-at-0 ; lem-tr-comm1-S-I-at-1 ; lem-tr-comm1-S-I-at-2 ; lem-tr-comm1-S-I-at-3 ; lem-tr-comm1-S-K0-at-0 ; lem-tr-comm1-S-K0-at-1 ; lem-tr-comm1-S-K0-at-2 ; lem-tr-comm1-S-K1-at-0 ; lem-tr-comm1-S-K1-at-1 ; lem-tr-comm1-S-K2-at-0 ; lem-tr-comm1-S-S0-at-0 ; lem-tr-comm1-S-S0-at-1 ; lem-tr-comm1-S-S0-at-2 ; lem-tr-comm1-S-S1-at-0 ; lem-tr-comm1-S-S1-at-1 ; lem-tr-comm1-S-S2-at-0 ; lem-tr-comm2-CS01-at-0 ; lem-tr-comm2-I-at-0 ; lem-tr-comm2-I-at-1 ; lem-tr-comm2-I-at-2 ; lem-tr-comm2-K0-at-0 ; lem-tr-comm2-K0-at-1 ; lem-tr-comm2-K1-at-0 ; lem-tr-comm2-S0-at-0 ; lem-tr-comm2-S0-at-1 ; lem-tr-comm2-S1-at-0 ; lem-tr-cx-ccz-at-0 ; lem-tr-rel-268-at-1 ; lem-tr-toff-ccz-at-0)

Inst : ∀ {w v} → 4 VRel, w === v → Set
Inst {w} {v} _ = ⟪ λʷ w ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ

record Missing : Set where
  field
    m-rel-269-0 : Inst (srel rel-269)
    m-rel-269-1 : Inst (cong↑ (srel rel-269))
    m-rel-272-0 : Inst (srel rel-272)
    m-rel-272-1 : Inst (cong↑ (srel rel-272))
    m-ck-tct-0 : Inst (srel ck-tct)
    m-lf-0 : Inst (srel lf)
    m-hyb-sq-0 : Inst (srel hyb-sq)
    m-hyb-yb-0 : Inst (srel hyb-yb)

λ-ax : Complete 4 → Missing → AxOk
λ-ax c4 ms (srel order-I) = lem-tr-order-I-at-0 c4
λ-ax c4 ms (cong↑ (srel order-I)) = lem-tr-order-I-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel order-I))) = lem-tr-order-I-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (srel order-I)))) = lem-tr-order-I-at-3 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (cong↑ (srel order-I))))) = lem-tr-order-I-at-4 c4
λ-ax c4 ms (srel order-S) = lem-tr-order-S-at-0 c4
λ-ax c4 ms (cong↑ (srel order-S)) = lem-tr-order-S-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel order-S))) = lem-tr-order-S-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (srel order-S)))) = lem-tr-order-S-at-3 c4
λ-ax c4 ms (srel order-K) = lem-tr-order-K-at-0 c4
λ-ax c4 ms (cong↑ (srel order-K)) = lem-tr-order-K-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel order-K))) = lem-tr-order-K-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (srel order-K)))) = lem-tr-order-K-at-3 c4
λ-ax c4 ms (srel order-SK) = lem-tr-order-SK-at-0 c4
λ-ax c4 ms (cong↑ (srel order-SK)) = lem-tr-order-SK-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel order-SK))) = lem-tr-order-SK-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (srel order-SK)))) = lem-tr-order-SK-at-3 c4
λ-ax c4 ms (srel order-CS) = lem-tr-order-CS-at-0 c4
λ-ax c4 ms (cong↑ (srel order-CS)) = lem-tr-order-CS-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel order-CS))) = lem-tr-order-CS-at-2 c4
λ-ax c4 ms (srel comm-CS-S₀) = lem-tr-comm-CS-S0-at-0 c4
λ-ax c4 ms (cong↑ (srel comm-CS-S₀)) = lem-tr-comm-CS-S0-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel comm-CS-S₀))) = lem-tr-comm-CS-S0-at-2 c4
λ-ax c4 ms (srel comm-CS-S₁) = lem-tr-comm-CS-S1-at-0 c4
λ-ax c4 ms (cong↑ (srel comm-CS-S₁)) = lem-tr-comm-CS-S1-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel comm-CS-S₁))) = lem-tr-comm-CS-S1-at-2 c4
λ-ax c4 ms (srel X-CS₀) = lem-tr-X-CS0-at-0 c4
λ-ax c4 ms (cong↑ (srel X-CS₀)) = lem-tr-X-CS0-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel X-CS₀))) = lem-tr-X-CS0-at-2 c4
λ-ax c4 ms (srel X-CS₁) = lem-tr-X-CS1-at-0 c4
λ-ax c4 ms (cong↑ (srel X-CS₁)) = lem-tr-X-CS1-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel X-CS₁))) = lem-tr-X-CS1-at-2 c4
λ-ax c4 ms (srel CS-K₀) = lem-tr-CS-K0-at-0 c4
λ-ax c4 ms (cong↑ (srel CS-K₀)) = lem-tr-CS-K0-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel CS-K₀))) = lem-tr-CS-K0-at-2 c4
λ-ax c4 ms (srel CS-K₁) = lem-tr-CS-K1-at-0 c4
λ-ax c4 ms (cong↑ (srel CS-K₁)) = lem-tr-CS-K1-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (srel CS-K₁))) = lem-tr-CS-K1-at-2 c4
λ-ax c4 ms (srel comm-CS↑-CS) = lem-tr-comm-CS-CS-at-0 c4
λ-ax c4 ms (cong↑ (srel comm-CS↑-CS)) = lem-tr-comm-CS-CS-at-1 c4
λ-ax c4 ms (srel rel-266) = lem-tr-rel-266-at-0 c4
λ-ax c4 ms (cong↑ (srel rel-266)) = lem-tr-rel-266-at-1 c4
λ-ax c4 ms (srel rel-267) = lem-tr-rel-267-at-0 c4
λ-ax c4 ms (cong↑ (srel rel-267)) = lem-tr-rel-267-at-1 c4
λ-ax c4 ms (srel rel-268) = lem-tr-rel-268-at-0 c4
λ-ax c4 ms (cong↑ (srel rel-268)) = lem-tr-rel-268-at-1 c4
λ-ax c4 ms (srel rel-269) = Missing.m-rel-269-0 ms
λ-ax c4 ms (cong↑ (srel rel-269)) = Missing.m-rel-269-1 ms
λ-ax c4 ms (srel rel-272) = Missing.m-rel-272-0 ms
λ-ax c4 ms (cong↑ (srel rel-272)) = Missing.m-rel-272-1 ms
λ-ax c4 ms (srel cx-ccz) = lem-tr-cx-ccz-at-0 c4
λ-ax c4 ms (srel toff-ccz) = lem-tr-toff-ccz-at-0 c4
λ-ax c4 ms (srel ck-tct) = Missing.m-ck-tct-0 ms
λ-ax c4 ms (comm₁ S-gate (gate₀ I-gate)) = lem-tr-comm1-S-I-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₀ I-gate ↥)) = lem-tr-comm1-S-I-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₀ I-gate ↥ ↥)) = lem-tr-comm1-S-I-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₀ I-gate ↥ ↥ ↥)) = lem-tr-comm1-S-I-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₁ S-gate)) = lem-tr-comm1-S-S0-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₁ K-gate)) = lem-tr-comm1-S-K0-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₁ S-gate ↥)) = lem-tr-comm1-S-S1-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₁ K-gate ↥)) = lem-tr-comm1-S-K1-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₁ S-gate ↥ ↥)) = lem-tr-comm1-S-S2-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₁ K-gate ↥ ↥)) = lem-tr-comm1-S-K2-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₂ CS-gate)) = lem-tr-comm1-S-CS01-at-0 c4
λ-ax c4 ms (comm₁ S-gate (gate₂ CS-gate ↥)) = lem-tr-comm1-S-CS12-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₀ I-gate)) = lem-tr-comm1-K-I-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₀ I-gate ↥)) = lem-tr-comm1-K-I-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₀ I-gate ↥ ↥)) = lem-tr-comm1-K-I-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₀ I-gate ↥ ↥ ↥)) = lem-tr-comm1-K-I-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₁ S-gate)) = lem-tr-comm1-K-S0-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₁ K-gate)) = lem-tr-comm1-K-K0-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₁ S-gate ↥)) = lem-tr-comm1-K-S1-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₁ K-gate ↥)) = lem-tr-comm1-K-K1-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₁ S-gate ↥ ↥)) = lem-tr-comm1-K-S2-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₁ K-gate ↥ ↥)) = lem-tr-comm1-K-K2-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₂ CS-gate)) = lem-tr-comm1-K-CS01-at-0 c4
λ-ax c4 ms (comm₁ K-gate (gate₂ CS-gate ↥)) = lem-tr-comm1-K-CS12-at-0 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₀ I-gate))) = lem-tr-comm1-S-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₀ I-gate ↥))) = lem-tr-comm1-S-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₀ I-gate ↥ ↥))) = lem-tr-comm1-S-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₁ S-gate))) = lem-tr-comm1-S-S0-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₁ K-gate))) = lem-tr-comm1-S-K0-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₁ S-gate ↥))) = lem-tr-comm1-S-S1-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₁ K-gate ↥))) = lem-tr-comm1-S-K1-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ S-gate (gate₂ CS-gate))) = lem-tr-comm1-S-CS01-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₀ I-gate))) = lem-tr-comm1-K-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₀ I-gate ↥))) = lem-tr-comm1-K-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₀ I-gate ↥ ↥))) = lem-tr-comm1-K-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₁ S-gate))) = lem-tr-comm1-K-S0-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₁ K-gate))) = lem-tr-comm1-K-K0-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₁ S-gate ↥))) = lem-tr-comm1-K-S1-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₁ K-gate ↥))) = lem-tr-comm1-K-K1-at-1 c4
λ-ax c4 ms (cong↑ (comm₁ K-gate (gate₂ CS-gate))) = lem-tr-comm1-K-CS01-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ S-gate (gate₀ I-gate)))) = lem-tr-comm1-S-I-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ S-gate (gate₀ I-gate ↥)))) = lem-tr-comm1-S-I-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ S-gate (gate₁ S-gate)))) = lem-tr-comm1-S-S0-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ S-gate (gate₁ K-gate)))) = lem-tr-comm1-S-K0-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ K-gate (gate₀ I-gate)))) = lem-tr-comm1-K-I-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ K-gate (gate₀ I-gate ↥)))) = lem-tr-comm1-K-I-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ K-gate (gate₁ S-gate)))) = lem-tr-comm1-K-S0-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₁ K-gate (gate₁ K-gate)))) = lem-tr-comm1-K-K0-at-2 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (comm₁ S-gate (gate₀ I-gate))))) = lem-tr-comm1-S-I-at-3 c4
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (comm₁ K-gate (gate₀ I-gate))))) = lem-tr-comm1-K-I-at-3 c4
λ-ax c4 ms (comm₂ CS-gate (gate₀ I-gate)) = lem-tr-comm2-I-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₀ I-gate ↥)) = lem-tr-comm2-I-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₀ I-gate ↥ ↥)) = lem-tr-comm2-I-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₁ S-gate)) = lem-tr-comm2-S0-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₁ K-gate)) = lem-tr-comm2-K0-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₁ S-gate ↥)) = lem-tr-comm2-S1-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₁ K-gate ↥)) = lem-tr-comm2-K1-at-0 c4
λ-ax c4 ms (comm₂ CS-gate (gate₂ CS-gate)) = lem-tr-comm2-CS01-at-0 c4
λ-ax c4 ms (cong↑ (comm₂ CS-gate (gate₀ I-gate))) = lem-tr-comm2-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₂ CS-gate (gate₀ I-gate ↥))) = lem-tr-comm2-I-at-1 c4
λ-ax c4 ms (cong↑ (comm₂ CS-gate (gate₁ S-gate))) = lem-tr-comm2-S0-at-1 c4
λ-ax c4 ms (cong↑ (comm₂ CS-gate (gate₁ K-gate))) = lem-tr-comm2-K0-at-1 c4
λ-ax c4 ms (cong↑ (cong↑ (comm₂ CS-gate (gate₀ I-gate)))) = lem-tr-comm2-I-at-2 c4
λ-ax c4 ms (srel lf) = Missing.m-lf-0 ms
λ-ax c4 ms (srel hyb-sq) = Missing.m-hyb-sq-0 ms
λ-ax c4 ms (srel hyb-yb) = Missing.m-hyb-yb-0 ms
λ-ax c4 ms (ω↑=ω I-gate) = refl
λ-ax c4 ms (cong↑ (ω↑=ω I-gate)) = refl
λ-ax c4 ms (cong↑ (cong↑ (ω↑=ω I-gate))) = refl
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (ω↑=ω I-gate)))) = refl
