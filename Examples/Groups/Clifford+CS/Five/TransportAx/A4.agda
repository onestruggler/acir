------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport on five wires: the axiom instances under 4 cong↑
--
-- The equations Inst of the instances of depth 4 (Five.TransportAx).
-- Written by `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.TransportAx.A4 where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.WinInst using (ws)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport
open import Examples.Groups.Clifford+CS.Five.TransportAx.Base using (Inst ; Missing ; m-ck-tct-0 ; m-lf-0 ; m-hyb-sq-0 ; m-hyb-yb-0)
open import Examples.Groups.Clifford+CS.Five.D.D200 using (lem-tr-order-I-at-4)

ax-s4 : Complete 4 → Missing → ∀ {w v} (a : 0 SRel, w === v) → Inst (cong↑ (cong↑ (cong↑ (cong↑ (srel a)))))
ax-s4 c4 ms order-I = lem-tr-order-I-at-4 (ws c4)
