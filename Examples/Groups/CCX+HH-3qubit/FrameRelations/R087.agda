{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R087 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At34 as At34

step0 : t34 • m0 ≈ X34 • M0
step0 = by-assoc-and (cong (At34.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t34 ≈ M0 • X34
step1 = by-assoc-and (cong (Am0.proved) (At34.proved)) Eq.refl Eq.refl

proved : X34 • M0 ≈ M0 • X34
proved = trans (sym (step0)) (trans (axiom r087) (step1))
