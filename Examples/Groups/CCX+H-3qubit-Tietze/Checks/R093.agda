{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R093 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e167 ; e168)

checked : scaledM (t67 • NK) (NK • t67) ≡ scaledM (NK • t67) (t67 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t67))) e167)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t67 • NK))) e168)))
