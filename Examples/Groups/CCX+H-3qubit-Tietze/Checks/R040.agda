{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R040 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e104 ; e105)

checked : scaledM (CZ01 • CZ12) (CZ12 • CZ01) ≡ scaledM (CZ12 • CZ01) (CZ01 • CZ12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CZ12 • CZ01))) e104)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CZ01 • CZ12))) e105)))
