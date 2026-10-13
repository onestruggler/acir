{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00924 as MV00924
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00925 as MV00925
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • M7 ≈ M7 • X34
proved = GL.•-cancelʳ {g = X34 • M7} {g' = M7 • X34} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00924.proved (MV00925.proved))) (trans (cong refl Base.proved) (move-product MV00925.proved (MV00924.proved))))
