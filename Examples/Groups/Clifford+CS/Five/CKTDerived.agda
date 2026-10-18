------------------------------------------------------------------------
-- Presentations of groups
--
-- λ(ck-tct) derived on five wires
--
-- Branch v-office's derivation of the controlled ck-tct (its
-- scratchpad/joint/ckt2.py: the joint paper's Proposition three, by
-- de-borrowing over transported two-wire equations, of the rule as
-- Syntactics states it) lives in FiveV/, over FiveV.Rules — the rules of
-- Syntactics and AX, nothing else — so it does not use the rule
-- λ-ck-tct.  Its theory embeds in Five.Rules' (`emb`), and so the
-- instance of Five.TransportAx.Base that Five.MissingInst takes from
-- λ-ck-tct is a theorem given completeness on four wires
-- (`ck-tct-derived`).
-- Written by v-office's scratchpad/five/port_ccs.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.CKTDerived where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (Word)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Rules
open import Examples.Groups.Clifford+CS.Five.Chain using (_≈_ ; trans ; by-assoc)
open import Examples.Groups.Clifford+CS.Five.TransportAx.Base using (Inst)
import Examples.Groups.Clifford+CS.FiveV.Rules as V
import Examples.Groups.Clifford+CS.FiveV.D.D219 as VD
open import Examples.Groups.Clifford+CS.FiveV.WinInst using (ws)

private
  variable
    n : ℕ
    w v : Word (Gen n)

-- FiveV's theory is a part of this one.
emb-rel : n V.XRel, w === v → n XRel, w === v
emb-rel (V.old r) = old r
emb-rel V.ax      = ax

emb-ax : n V.XVRel, w === v → n XVRel, w === v
emb-ax (V.srelₓ r)     = srelₓ (emb-rel r)
emb-ax (V.cong↑ₓ a)    = cong↑ₓ (emb-ax a)
emb-ax (V.comm₁ₓ h g)  = comm₁ₓ h g
emb-ax (V.comm₂ₓ h g)  = comm₂ₓ h g
emb-ax (V.ω↑=ωₓ h)     = ω↑=ωₓ h

emb : n V.⊢ₓ w ≈ v → n ⊢ₓ w ≈ v
emb PB.refl          = PB.refl
emb (PB.sym e)       = PB.sym (emb e)
emb (PB.trans e e′)  = PB.trans (emb e) (emb e′)
emb (PB.cong e e′)   = PB.cong (emb e) (emb e′)
emb PB.assoc         = PB.assoc
emb PB.left-unit     = PB.left-unit
emb PB.right-unit    = PB.right-unit
emb (PB.axiom a)     = PB.axiom (emb-ax a)

-- λ(ck-tct), in the form Five.MissingInst gives it.
ck-tct-derived : Complete 4 → Inst (srel ck-tct)
ck-tct-derived c4 = trans (by-assoc Eq.refl) (trans (emb (VD.lem-F1-ck-tctat0 (ws c4))) (by-assoc Eq.refl))
