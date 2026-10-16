------------------------------------------------------------------------
-- Presentations of groups
--
-- The transport of the four-wire rules not derived on five wires
--
-- Five.TransportAx takes the λ-images of the instances its derivations do
-- not cover (`Missing`): those of the four-wire rules ck-tct, lf, hyb-sq
-- and hyb-yb.  They are the five-wire rules λ(ck-tct), λ(lf), λ(hyb-sq),
-- λ(hyb-yb) of Five.Rules, up to the bracketing of λ¹ (`λʷ≈λc`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.MissingInst where

open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_,_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
  using (Circuit ; module LF ; module HSQ ; module HYB)
open import Examples.Groups.Clifford+CS.Five.Rules
  using (_XRel,_===_ ; srelₓ ; λ-lf ; λ-hyb-sq ; λ-hyb-yb ; λ-ck-tct ; module CKT)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λc)
open import Examples.Groups.Clifford+CS.Five.Transport using (λʷ)
open import Examples.Groups.Clifford+CS.Five.TransportAx using (Missing)

-- λ¹ as a line of letters is λ¹ as a circuit.
λʷ≈λc : ∀ w → ⟪ λʷ w ⟫ʷ ≈ λc w
λʷ≈λc [ g ]ʷ  = refl
λʷ≈λc ε       = refl
λʷ≈λc (u • v) = trans (⟪⟫-++ (λʷ u) (λʷ v)) (cong (λʷ≈λc u) (λʷ≈λc v))

private
  by-rule : ∀ {u v : Circuit 4} → 5 XRel, λc u === λc v → ⟪ λʷ u ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ
  by-rule {u} {v} a = trans (λʷ≈λc u) (trans (PB.axiom (srelₓ a)) (sym (λʷ≈λc v)))

-- In the order of Missing's components: ck-tct, lf, hyb-sq, hyb-yb.
missing : Missing
missing = by-rule {CKT.l} {CKT.r} λ-ck-tct
        , by-rule {LF.Hyb} {LF.Dec} λ-lf
        , by-rule {HSQ.Sq} {ε} λ-hyb-sq
        , by-rule {HYB.Yl} {HYB.Yr} λ-hyb-yb
