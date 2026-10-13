{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00800 as MV00800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00801 as MV00801
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • M5 ≈ M5 • X13
proved = GL.•-cancelʳ {g = X13 • M5} {g' = M5 • X13} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
  (trans (sym (move-product MV00800.proved (MV00801.proved))) (trans (cong refl Base.proved) (move-product MV00801.proved (MV00800.proved))))
