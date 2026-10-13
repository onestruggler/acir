{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak0124 as Ak0124
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak1345 as Ak1345
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak2345 as Ak2345

step0 : NK • k1345 ≈ K0123 • K1345
step0 = by-assoc-and (cong (ANK.proved) (Ak1345.proved)) Eq.refl Eq.refl

step1 : k2345 • k0124 ≈ K2345 • K0124
step1 = by-assoc-and (cong (Ak2345.proved) (Ak0124.proved)) Eq.refl Eq.refl

proved : K0123 • K1345 ≈ K2345 • K0124
proved = trans (sym (step0)) (trans (axiom r100) (step1))
