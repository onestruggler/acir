{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij241367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01414 as MV01414
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01415 as MV01415
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K1367 ≈ K1367 • X24
proved = GL.•-cancelʳ {g = X24 • K1367} {g' = K1367 • X24} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01414.proved (MV01415.proved))) (trans (cong refl Base.proved) (move-product MV01415.proved (MV01414.proved))))
