{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R090 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At67 as At67

step0 : t67 • m0 ≈ X67 • M0
step0 = by-assoc-and (cong (At67.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t67 ≈ M0 • X67
step1 = by-assoc-and (cong (Am0.proved) (At67.proved)) Eq.refl Eq.refl

proved : X67 • M0 ≈ M0 • X67
proved = trans (sym (step0)) (trans (axiom r090) (step1))
