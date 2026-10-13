{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6703 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00030 as E

proved : X67 • X03 ≈ X03 • X67
proved = by-assoc-and E.proved Eq.refl Eq.refl
