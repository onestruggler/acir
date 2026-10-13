{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R092 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At56 as At56

step0 : t56 • NK ≈ X56 • K0123
step0 = by-assoc-and (cong (At56.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • t56 ≈ K0123 • X56
step1 = by-assoc-and (cong (ANK.proved) (At56.proved)) Eq.refl Eq.refl

proved : X56 • K0123 ≈ K0123 • X56
proved = trans (sym (step0)) (trans (axiom r092) (step1))
