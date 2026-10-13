{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00008 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine

proved : p (s3 • s2 • s1 • s2 • s3) • m0 ≈ m0 • p (s3 • s2 • s1 • s2 • s3)
proved = commute-product (axiom r087) (commute-product (axiom r086) (commute-product (axiom r085) (commute-product (axiom r086) (axiom r087))))
