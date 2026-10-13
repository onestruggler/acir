{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01510 as MV01510
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K0126 ≈ K0126 • X34
proved = GL.•-cancelʳ {g = X34 • K0126} {g' = K0126 • X34} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV01510.proved (MV00643.proved))) (trans (cong refl Base.proved) (move-product MV00643.proved (MV01510.proved))))
