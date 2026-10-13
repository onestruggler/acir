{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At12 as At12

step0 : t12 • m0 ≈ X12 • M0
step0 = by-assoc-and (cong (At12.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t12 ≈ M0 • X12
step1 = by-assoc-and (cong (Am0.proved) (At12.proved)) Eq.refl Eq.refl

proved : X12 • M0 ≈ M0 • X12
proved = trans (sym (step0)) (trans (axiom r085) (step1))
