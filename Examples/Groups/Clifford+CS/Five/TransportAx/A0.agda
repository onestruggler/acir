------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport on five wires: the axiom instances under 0 cong↑
--
-- The equations Inst of the instances of depth 0 (Five.TransportAx).
-- Written by `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.TransportAx.A0 where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.WinInst using (ws)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport
open import Examples.Groups.Clifford+CS.Five.TransportAx.Base using (Inst ; Missing ; m-ck-tct-0 ; m-lf-0 ; m-hyb-sq-0 ; m-hyb-yb-0)
open import Examples.Groups.Clifford+CS.Five.D.D200 using (lem-tr-comm-CS-CS-at-0)
open import Examples.Groups.Clifford+CS.Five.D.D201 using (lem-tr-comm1-K-CS01-at-0 ; lem-tr-comm1-K-CS12-at-0 ; lem-tr-comm1-K-K1-at-0 ; lem-tr-comm1-K-K2-at-0 ; lem-tr-comm1-K-S1-at-0 ; lem-tr-comm1-K-S2-at-0 ; lem-tr-comm1-S-CS01-at-0 ; lem-tr-comm1-S-CS12-at-0 ; lem-tr-comm1-S-K1-at-0 ; lem-tr-comm1-S-K2-at-0 ; lem-tr-comm1-S-S1-at-0 ; lem-tr-comm1-S-S2-at-0 ; lem-tr-comm2-CS01-at-0 ; lem-tr-comm2-K0-at-0 ; lem-tr-comm2-K1-at-0 ; lem-tr-comm2-S0-at-0 ; lem-tr-comm2-S1-at-0 ; lem-tr-cx-ccz-at-0 ; lem-tr-rel-266-at-0 ; lem-tr-rel-267-at-0 ; lem-tr-rel-268-at-0 ; lem-tr-rel-269-at-0 ; lem-tr-rel-272-at-0 ; lem-tr-toff-ccz-at-0)
open import Examples.Groups.Clifford+CS.Five.D.TRL using (lem-tr-CS-K0-at-0 ; lem-tr-CS-K1-at-0 ; lem-tr-X-CS0-at-0 ; lem-tr-X-CS1-at-0 ; lem-tr-comm-CS-S0-at-0 ; lem-tr-comm-CS-S1-at-0 ; lem-tr-comm1-K-I-at-0 ; lem-tr-comm1-K-K0-at-0 ; lem-tr-comm1-K-S0-at-0 ; lem-tr-comm1-S-I-at-0 ; lem-tr-comm1-S-K0-at-0 ; lem-tr-comm1-S-S0-at-0 ; lem-tr-comm2-I-at-0 ; lem-tr-order-CS-at-0 ; lem-tr-order-I-at-0 ; lem-tr-order-K-at-0 ; lem-tr-order-S-at-0 ; lem-tr-order-SK-at-0)

ax-s0 : Complete 4 → Missing → ∀ {w v} (a : 4 SRel, w === v) → Inst (srel a)
ax-s0 c4 ms order-I = lem-tr-order-I-at-0 (ws c4)
ax-s0 c4 ms order-S = lem-tr-order-S-at-0 (ws c4)
ax-s0 c4 ms order-K = lem-tr-order-K-at-0 (ws c4)
ax-s0 c4 ms order-SK = lem-tr-order-SK-at-0 (ws c4)
ax-s0 c4 ms order-CS = lem-tr-order-CS-at-0 (ws c4)
ax-s0 c4 ms comm-CS-S₀ = lem-tr-comm-CS-S0-at-0 (ws c4)
ax-s0 c4 ms comm-CS-S₁ = lem-tr-comm-CS-S1-at-0 (ws c4)
ax-s0 c4 ms X-CS₀ = lem-tr-X-CS0-at-0 (ws c4)
ax-s0 c4 ms X-CS₁ = lem-tr-X-CS1-at-0 (ws c4)
ax-s0 c4 ms CS-K₀ = lem-tr-CS-K0-at-0 (ws c4)
ax-s0 c4 ms CS-K₁ = lem-tr-CS-K1-at-0 (ws c4)
ax-s0 c4 ms comm-CS↑-CS = lem-tr-comm-CS-CS-at-0 (ws c4)
ax-s0 c4 ms rel-266 = lem-tr-rel-266-at-0 (ws c4)
ax-s0 c4 ms rel-267 = lem-tr-rel-267-at-0 (ws c4)
ax-s0 c4 ms rel-268 = lem-tr-rel-268-at-0 (ws c4)
ax-s0 c4 ms rel-269 = lem-tr-rel-269-at-0 (ws c4)
ax-s0 c4 ms rel-272 = lem-tr-rel-272-at-0 (ws c4)
ax-s0 c4 ms cx-ccz = lem-tr-cx-ccz-at-0 (ws c4)
ax-s0 c4 ms toff-ccz = lem-tr-toff-ccz-at-0 (ws c4)
ax-s0 c4 ms ck-tct = m-ck-tct-0 ms
ax-s0 c4 ms lf = m-lf-0 ms
ax-s0 c4 ms hyb-sq = m-hyb-sq-0 ms
ax-s0 c4 ms hyb-yb = m-hyb-yb-0 ms

ax-k1-0 : Complete 4 → ∀ h (g : Gen 3) → Inst (comm₁ h g)
ax-k1-0 c4 S-gate (gate₀ I-gate) = lem-tr-comm1-S-I-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₀ I-gate ↥) = lem-tr-comm1-S-I-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₀ I-gate ↥ ↥) = lem-tr-comm1-S-I-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₀ I-gate ↥ ↥ ↥) = lem-tr-comm1-S-I-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₁ S-gate) = lem-tr-comm1-S-S0-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₁ K-gate) = lem-tr-comm1-S-K0-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₁ S-gate ↥) = lem-tr-comm1-S-S1-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₁ K-gate ↥) = lem-tr-comm1-S-K1-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₁ S-gate ↥ ↥) = lem-tr-comm1-S-S2-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₁ K-gate ↥ ↥) = lem-tr-comm1-S-K2-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₂ CS-gate) = lem-tr-comm1-S-CS01-at-0 (ws c4)
ax-k1-0 c4 S-gate (gate₂ CS-gate ↥) = lem-tr-comm1-S-CS12-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₀ I-gate) = lem-tr-comm1-K-I-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₀ I-gate ↥) = lem-tr-comm1-K-I-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₀ I-gate ↥ ↥) = lem-tr-comm1-K-I-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₀ I-gate ↥ ↥ ↥) = lem-tr-comm1-K-I-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₁ S-gate) = lem-tr-comm1-K-S0-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₁ K-gate) = lem-tr-comm1-K-K0-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₁ S-gate ↥) = lem-tr-comm1-K-S1-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₁ K-gate ↥) = lem-tr-comm1-K-K1-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₁ S-gate ↥ ↥) = lem-tr-comm1-K-S2-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₁ K-gate ↥ ↥) = lem-tr-comm1-K-K2-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₂ CS-gate) = lem-tr-comm1-K-CS01-at-0 (ws c4)
ax-k1-0 c4 K-gate (gate₂ CS-gate ↥) = lem-tr-comm1-K-CS12-at-0 (ws c4)

ax-k2-0 : Complete 4 → ∀ h (g : Gen 2) → Inst (comm₂ h g)
ax-k2-0 c4 CS-gate (gate₀ I-gate) = lem-tr-comm2-I-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₀ I-gate ↥) = lem-tr-comm2-I-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₀ I-gate ↥ ↥) = lem-tr-comm2-I-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₁ S-gate) = lem-tr-comm2-S0-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₁ K-gate) = lem-tr-comm2-K0-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₁ S-gate ↥) = lem-tr-comm2-S1-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₁ K-gate ↥) = lem-tr-comm2-K1-at-0 (ws c4)
ax-k2-0 c4 CS-gate (gate₂ CS-gate) = lem-tr-comm2-CS01-at-0 (ws c4)
