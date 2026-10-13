{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij165 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00838 as MV00838
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00839 as MV00839
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • M5 ≈ M5 • X16
proved = GL.•-cancelʳ {g = X16 • M5} {g' = M5 • X16} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00838.proved (MV00839.proved))) (trans (cong refl Base.proved) (move-product MV00839.proved (MV00838.proved))))
