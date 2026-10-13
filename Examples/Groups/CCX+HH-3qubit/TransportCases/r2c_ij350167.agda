{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350167 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01544 as MV01544
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01545 as MV01545
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0167 ≈ K0167 • X35
proved = GL.•-cancelʳ {g = X35 • K0167} {g' = K0167 • X35} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01544.proved (MV01545.proved))) (trans (cong refl Base.proved) (move-product MV01545.proved (MV01544.proved))))
