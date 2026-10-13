{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij162345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01329 as MV01329
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01330 as MV01330
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K2345 ≈ K2345 • X16
proved = GL.•-cancelʳ {g = X16 • K2345} {g' = K2345 • X16} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01329.proved (MV01330.proved))) (trans (cong refl Base.proved) (move-product MV01330.proved (MV01329.proved))))
