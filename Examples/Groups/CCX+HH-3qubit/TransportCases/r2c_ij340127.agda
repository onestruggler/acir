{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00644 as MV00644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01511 as MV01511
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K0127 ≈ K0127 • X34
proved = GL.•-cancelʳ {g = X34 • K0127} {g' = K0127 • X34} {h = p (s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01511.proved (MV00644.proved))) (trans (cong refl Base.proved) (move-product MV00644.proved (MV01511.proved))))
