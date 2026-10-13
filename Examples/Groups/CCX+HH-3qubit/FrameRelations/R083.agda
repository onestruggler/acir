{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0

step0 : m0 • m0 ≈ M0 • M0
step0 = by-assoc-and (cong (Am0.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : ε ≈ ε
step1 = by-assoc-and (refl {w = ε}) Eq.refl Eq.refl

proved : M0 • M0 ≈ ε
proved = trans (sym (step0)) (trans (axiom r083) (step1))
