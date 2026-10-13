{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01479 as MV01479
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01480 as MV01480
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K0134 ≈ K0134 • X27
proved = GL.•-cancelʳ {g = X27 • K0134} {g' = K0134 • X27} {h = p (s2 • s3 • s6 • s5)}
  (trans (sym (move-product MV01479.proved (MV01480.proved))) (trans (cong refl Base.proved) (move-product MV01480.proved (MV01479.proved))))
