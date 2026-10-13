{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0256 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02869 as MV02869
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02870 as MV02870
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K0256 ≈ M0 • K0256 • M0 • K0256 • M0
proved = GL.•-cancelʳ {g = X25 • K0256} {g' = M0 • K0256 • M0 • K0256 • M0} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02869.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV02870.proved (move-product MV00662.proved (move-product MV02870.proved (move-product MV00662.proved (MV02870.proved)))))))
