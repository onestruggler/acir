{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00920 as MV00920
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00921 as MV00921
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • M5 ≈ M5 • X34
proved = GL.•-cancelʳ {g = X34 • M5} {g' = M5 • X34} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00920.proved (MV00921.proved))) (trans (cong refl Base.proved) (move-product MV00921.proved (MV00920.proved))))
