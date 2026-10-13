{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At12 as At12

step0 : t12 • NK ≈ X12 • K0123
step0 = by-assoc-and (cong (At12.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : m0 • NK • m0 • NK • m0 ≈ M0 • K0123 • M0 • K0123 • M0
step1 = by-assoc-and (cong (Am0.proved) (cong (ANK.proved) (cong (Am0.proved) (cong (ANK.proved) (Am0.proved))))) Eq.refl Eq.refl

proved : X12 • K0123 ≈ M0 • K0123 • M0 • K0123 • M0
proved = trans (sym (step0)) (trans (axiom r098) (step1))
