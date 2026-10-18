------------------------------------------------------------------------
-- Presentations of groups
--
-- The natural CCX+H rules with the schema.
--
-- The schema is CCX+HH.NaturalP.Schema's, read through θ: every
-- controlled version of CCX • CCX, built by the classical gadgets of
-- NaturalP.Ctrl, is ε.  Those gadgets use only X, CX, CCX and the swap,
-- which θ leaves as they are.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Schema where

open import Data.Nat.Base using (ℕ)
open import Word.Base using (ε)
open import Notations using (₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.NaturalP.Syntactics as NH public
  using (Gate ; X-gate ; H-gate ; CX-gate ; SW-gate ; CCX-gate ; X ; H ; CX ; CCX ; HHw ; XC ; CZ ; Z
        ; _NH,_===_)
open import Circuit.Prop Gate SW-gate public
open import Examples.Groups.CCX+HH.NaturalP.Schema using (CtrlCCX)
open import Examples.Groups.CCX+H.NaturalP.Theta using (θ)

private
  variable
    n k : ℕ
    w v : Circuit n

infix 4 _NHΣ,_===_
data _NHΣ,_===_ : (n : ℕ) → CRel n where
  nh  : n NH, w === v → n NHΣ, w === v
  sch : ∀ {w} → CtrlCCX k w → (₄₊ k) NHΣ, θ w === ε

open Lift-To-Prop _NHΣ,_===_ public

-- The natural rules embed.
emb-ax : n NH.VRel, w === v → n VRel, w === v
emb-ax (NH.srel (NH.σrel s)) = srel (σrel s)
emb-ax (NH.srel (NH.srel r)) = srel (srel (nh r))
emb-ax (NH.cong↑ y)          = cong↑ (emb-ax y)
emb-ax (NH.comm₁ h g)        = comm₁ h g
emb-ax (NH.comm₂ h g)        = comm₂ h g
emb-ax (NH.comm₃ h g)        = comm₃ h g
emb-ax (NH.ω↑=ω ())

emb : n NH.⊢ w ≈ v → n ⊢ w ≈ v
emb PB.refl        = PB.refl
emb (PB.sym p)     = PB.sym (emb p)
emb (PB.trans p q) = PB.trans (emb p) (emb q)
emb (PB.cong p q)  = PB.cong (emb p) (emb q)
emb PB.assoc       = PB.assoc
emb PB.left-unit   = PB.left-unit
emb PB.right-unit  = PB.right-unit
emb (PB.axiom x)   = PB.axiom (emb-ax x)
