{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij160 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00830 as MV00830
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00831 as MV00831
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • M0 ≈ M0 • X16
proved = GL.•-cancelʳ {g = X16 • M0} {g' = M0 • X16} {h = p (s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00830.proved (MV00831.proved))) (trans (cong refl Base.proved) (move-product MV00831.proved (MV00830.proved))))
