{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At45 as At45

step0 : t45 • NK ≈ X45 • K0123
step0 = by-assoc-and (cong (At45.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • t45 ≈ K0123 • X45
step1 = by-assoc-and (cong (ANK.proved) (At45.proved)) Eq.refl Eq.refl

proved : X45 • K0123 ≈ K0123 • X45
proved = trans (sym (step0)) (trans (axiom r091) (step1))
