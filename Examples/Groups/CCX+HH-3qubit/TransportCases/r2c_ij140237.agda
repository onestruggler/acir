{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01255 as MV01255
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X14 • K0237 ≈ K0237 • X14
proved = GL.•-cancelʳ {g = X14 • K0237} {g' = K0237 • X14} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01255.proved (MV00658.proved))) (trans (cong refl Base.proved) (move-product MV00658.proved (MV01255.proved))))
