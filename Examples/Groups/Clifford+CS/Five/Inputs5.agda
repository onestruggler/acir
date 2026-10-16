------------------------------------------------------------------------
-- Presentations of groups
--
-- The generated five-wire lemmas, assembled
--
-- Five.Inputs from the lemmas of Five.D: the λ-calculus at control
-- wire 4 (Five.CalcAx), the windows of (F6) and of the letters touching
-- wire 4 (Five.F6Ax), and the transport of every four-wire rule
-- (Five.TransportAx), which still takes the instances the derivations do
-- not cover (`Missing`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Inputs5 where

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.TransportAx using (Missing ; λ-ax)
import Examples.Groups.Clifford+CS.Five.CalcAx as CA
import Examples.Groups.Clifford+CS.Five.F6Ax as F6

inputs : Complete 4 → Missing → Inputs
inputs c4 ms = record
  { F4ᵍ   = CA.F4ᵍ c4
  ; F5ᵍ   = CA.F5ᵍ c4
  ; x4x4  = CA.x4x4 c4
  ; ok    = λ-ax c4 ms
  ; cx14ˡ = F6.cx14 c4
  ; w1ˡ   = F6.w1 c4
  ; w2ˡ   = F6.w2 c4
  ; aaˡ   = F6.aa c4
  ; eeˡ   = F6.ee c4
  ; sb2ˡ  = F6.sb2 c4
  ; cx43ˡ = F6.cx43 c4
  ; cx34ˡ = F6.cx34 c4
  ; sw34ˡ = F6.sw34 c4
  }
