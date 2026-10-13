{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am1 as Am1
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am3 as Am3
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At01 as At01
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At13 as At13

step0 : t01 • NK ≈ X01 • K0123
step0 = by-assoc-and (cong (At01.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • t13 • m1 • m3 ≈ K0123 • X13 • M1 • M3
step1 = by-assoc-and (cong (ANK.proved) (cong (At13.proved) (cong (Am1.proved) (Am3.proved)))) Eq.refl Eq.refl

proved : X01 • K0123 ≈ K0123 • X13 • M1 • M3
proved = trans (sym (step0)) (trans (axiom r097) (step1))
