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
-- `lem-tr-…` of Five.D, collected by depth in TransportAx/A0-A4.  What
-- the joint run does not derive is a field of `Missing`: the controlled
-- versions of the four-wire rules ck-tct, lf, hyb-sq and hyb-yb (rules
-- on five wires, the first derived: Five.CKTDerived; Five.MissingInst).
-- Written by `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.TransportAx where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport
open import Examples.Groups.Clifford+CS.Five.TransportAx.Base public using (Inst ; Missing ; m-ck-tct-0 ; m-lf-0 ; m-hyb-sq-0 ; m-hyb-yb-0)
open import Examples.Groups.Clifford+CS.Five.TransportAx.A0 using (ax-s0 ; ax-k1-0 ; ax-k2-0)
open import Examples.Groups.Clifford+CS.Five.TransportAx.A1 using (ax-s1 ; ax-k1-1 ; ax-k2-1)
open import Examples.Groups.Clifford+CS.Five.TransportAx.A2 using (ax-s2 ; ax-k1-2 ; ax-k2-2)
open import Examples.Groups.Clifford+CS.Five.TransportAx.A3 using (ax-s3 ; ax-k1-3)
open import Examples.Groups.Clifford+CS.Five.TransportAx.A4 using (ax-s4)

λ-ax : Complete 4 → Missing → AxOk
λ-ax c4 ms (srel a) = ax-s0 c4 ms a
λ-ax c4 ms (comm₁ h g) = ax-k1-0 c4 h g
λ-ax c4 ms (comm₂ h g) = ax-k2-0 c4 h g
λ-ax c4 ms (cong↑ (srel a)) = ax-s1 c4 ms a
λ-ax c4 ms (cong↑ (comm₁ h g)) = ax-k1-1 c4 h g
λ-ax c4 ms (cong↑ (comm₂ h g)) = ax-k2-1 c4 h g
λ-ax c4 ms (cong↑ (cong↑ (srel a))) = ax-s2 c4 ms a
λ-ax c4 ms (cong↑ (cong↑ (comm₁ h g))) = ax-k1-2 c4 h g
λ-ax c4 ms (cong↑ (cong↑ (comm₂ h g))) = ax-k2-2 c4 h g
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (srel a)))) = ax-s3 c4 ms a
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (comm₁ h g)))) = ax-k1-3 c4 h g
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (cong↑ (srel a))))) = ax-s4 c4 ms a
λ-ax c4 ms (ω↑=ω I-gate) = refl
λ-ax c4 ms (cong↑ (ω↑=ω I-gate)) = refl
λ-ax c4 ms (cong↑ (cong↑ (ω↑=ω I-gate))) = refl
λ-ax c4 ms (cong↑ (cong↑ (cong↑ (ω↑=ω I-gate)))) = refl
