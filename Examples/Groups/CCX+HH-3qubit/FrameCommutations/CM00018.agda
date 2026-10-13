{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00018 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine

proved : p (s6 • s5 • s6) • NK ≈ NK • p (s6 • s5 • s6)
proved = commute-product (axiom r093) (commute-product (axiom r092) (axiom r093))
