{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R086 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At23 as At23

step0 : t23 • m0 ≈ X23 • M0
step0 = by-assoc-and (cong (At23.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t23 ≈ M0 • X23
step1 = by-assoc-and (cong (Am0.proved) (At23.proved)) Eq.refl Eq.refl

proved : X23 • M0 ≈ M0 • X23
proved = trans (sym (step0)) (trans (axiom r086) (step1))
