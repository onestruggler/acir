------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport on five wires: the axiom instances under 3 cong↑
--
-- The equations Inst of the instances of depth 3 (Five.TransportAx).
-- Written by `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.TransportAx.A3 where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.WinInst using (ws)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport
open import Examples.Groups.Clifford+CS.Five.TransportAx.Base using (Inst ; Missing ; m-ck-tct-0 ; m-lf-0 ; m-hyb-sq-0 ; m-hyb-yb-0)
open import Examples.Groups.Clifford+CS.Five.D.D200 using (lem-tr-order-I-at-3 ; lem-tr-order-K-at-3 ; lem-tr-order-S-at-3 ; lem-tr-order-SK-at-3)
open import Examples.Groups.Clifford+CS.Five.D.D201 using (lem-tr-comm1-K-I-at-3 ; lem-tr-comm1-S-I-at-3)

ax-s3 : Complete 4 → Missing → ∀ {w v} (a : 1 SRel, w === v) → Inst (cong↑ (cong↑ (cong↑ (srel a))))
ax-s3 c4 ms order-I = lem-tr-order-I-at-3 (ws c4)
ax-s3 c4 ms order-S = lem-tr-order-S-at-3 (ws c4)
ax-s3 c4 ms order-K = lem-tr-order-K-at-3 (ws c4)
ax-s3 c4 ms order-SK = lem-tr-order-SK-at-3 (ws c4)

ax-k1-3 : Complete 4 → ∀ h (g : Gen 0) → Inst (cong↑ (cong↑ (cong↑ (comm₁ h g))))
ax-k1-3 c4 S-gate (gate₀ I-gate) = lem-tr-comm1-S-I-at-3 (ws c4)
ax-k1-3 c4 K-gate (gate₀ I-gate) = lem-tr-comm1-K-I-at-3 (ws c4)
