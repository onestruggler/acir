{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R089 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At56 as At56

step0 : t56 • m0 ≈ X56 • M0
step0 = by-assoc-and (cong (At56.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t56 ≈ M0 • X56
step1 = by-assoc-and (cong (Am0.proved) (At56.proved)) Eq.refl Eq.refl

proved : X56 • M0 ≈ M0 • X56
proved = trans (sym (step0)) (trans (axiom r089) (step1))
