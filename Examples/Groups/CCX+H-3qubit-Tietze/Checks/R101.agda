{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R101 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e239 ; e241)

checked : scaledM (m0 • m4 • t04 • rho) (rho • t04 • m4 • m0) ≡ scaledM (rho • t04 • m4 • m0) (m0 • m4 • t04 • rho)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (rho • t04 • m4 • m0))) e239)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (m0 • m4 • t04 • rho))) e241)))
