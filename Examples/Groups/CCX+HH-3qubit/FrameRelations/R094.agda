{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am4 as Am4

step0 : m4 • NK ≈ M4 • K0123
step0 = by-assoc-and (cong (Am4.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • m4 ≈ K0123 • M4
step1 = by-assoc-and (cong (ANK.proved) (Am4.proved)) Eq.refl Eq.refl

proved : M4 • K0123 ≈ K0123 • M4
proved = trans (sym (step0)) (trans (axiom r094) (step1))
