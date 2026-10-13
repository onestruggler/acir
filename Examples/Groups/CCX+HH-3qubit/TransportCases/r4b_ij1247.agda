{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02906 as MV02906
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02907 as MV02907
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K1247 ≈ M1 • K1247 • M1 • K1247 • M1
proved = GL.•-cancelʳ {g = X24 • K1247} {g' = M1 • K1247 • M1 • K1247 • M1} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02906.proved (MV00681.proved))) (trans (cong refl Base.proved) (move-product MV02907.proved (move-product MV00681.proved (move-product MV02907.proved (move-product MV00681.proved (MV02907.proved)))))))
