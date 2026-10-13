{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r6a_ij01234567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02452 as Move4
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03113 as Move0
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00959 as XX
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 as M0inv
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as MM
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R101 as Base
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij4 as M4inv

step0 : X04 • (M4 • M0) ≈ (M0 • M4) • X04
step0 = by-assoc-and (move-product Move4.proved Move0.proved) Eq.refl Eq.refl

step1 : X04 • M4 • M0 • X04 • M0 • M4 ≈ M0 • M4 • X04 • X04 • M0 • M4
step1 = by-assoc-and (cong step0 (refl {w = X04 • M0 • M4})) Eq.refl Eq.refl

step2 : M0 • M4 • X04 • X04 • M0 • M4 ≈ M0 • M4 • M0 • M4
step2 = by-assoc-and (under (M0 • M4) (M0 • M4) (by-assoc-and XX.proved Eq.refl Eq.refl)) Eq.refl Eq.refl

step3 : M0 • M4 • M0 • M4 ≈ M0 • M0 • M4 • M4
step3 = by-assoc-and (under M0 M4 (sym MM.proved)) Eq.refl Eq.refl

step4 : M0 • M0 • M4 • M4 ≈ ε
step4 = by-assoc-and (cong M0inv.proved M4inv.proved) Eq.refl Eq.refl

step5 : X04 • M4 • M0 • X04 • M0 • M4 ≈ ε
step5 = trans step1 (trans step2 (trans step3 step4))

step6 : M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567 • X04 • M0 • M4 ≈ (K4567 • K0123 • X34 • K0123 • K4567) • (X04 • M4 • M0 • X04 • M0 • M4)
step6 = by-assoc-and (cong Base.proved (refl {w = X04 • M0 • M4})) Eq.refl Eq.refl

proved : M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567 • X04 • M0 • M4 ≈ K4567 • K0123 • X34 • K0123 • K4567
proved = trans step6 (trans (cong (refl {w = K4567 • K0123 • X34 • K0123 • K4567}) step5) right-unit)
