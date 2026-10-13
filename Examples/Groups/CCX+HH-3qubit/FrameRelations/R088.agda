{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R088 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At45 as At45

step0 : t45 • m0 ≈ X45 • M0
step0 = by-assoc-and (cong (At45.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t45 ≈ M0 • X45
step1 = by-assoc-and (cong (Am0.proved) (At45.proved)) Eq.refl Eq.refl

proved : X45 • M0 ≈ M0 • X45
proved = trans (sym (step0)) (trans (axiom r088) (step1))
