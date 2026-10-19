------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport on five wires: the statement for one axiom instance
--
-- `Inst a`, the equation of the λ¹₄-images of the two sides of an axiom
-- instance a of the four-wire theory, and `Missing`, those the joint
-- run does not derive: the controlled versions of the four-wire rules
-- ck-tct, lf, hyb-sq and hyb-yb (rules on five wires, the first derived:
-- Five.CKTDerived; Five.MissingInst).  Written by
-- `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.TransportAx.Base where

open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Transport

Inst : ∀ {w v} → 4 VRel, w === v → Set
Inst {w} {v} _ = ⟪ λʷ w ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ

-- A product, not a record: the positivity checker normalises the types
-- of a record's fields, here the λ-images of the four-wire rules, and
-- that took more than 5 GB.
Missing : Set
Missing = Inst (srel ck-tct) × Inst (srel lf) × Inst (srel hyb-sq) × Inst (srel hyb-yb)

m-ck-tct-0 : Missing → Inst (srel ck-tct)
m-ck-tct-0 m = proj₁ m

m-lf-0 : Missing → Inst (srel lf)
m-lf-0 m = proj₁ (proj₂ m)

m-hyb-sq-0 : Missing → Inst (srel hyb-sq)
m-hyb-sq-0 m = proj₁ (proj₂ (proj₂ m))

m-hyb-yb-0 : Missing → Inst (srel hyb-yb)
m-hyb-yb-0 m = proj₂ (proj₂ (proj₂ m))

