{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK

step0 : NK • NK ≈ K0123 • K0123
step0 = by-assoc-and (cong (ANK.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : ε ≈ ε
step1 = by-assoc-and (refl {w = ε}) Eq.refl Eq.refl

proved : K0123 • K0123 ≈ ε
proved = trans (sym (step0)) (trans (axiom r084) (step1))
