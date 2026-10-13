{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01568 as MV01568
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01569 as MV01569
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • K0127 ≈ K0127 • X36
proved = GL.•-cancelʳ {g = X36 • K0127} {g' = K0127 • X36} {h = p (s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01568.proved (MV01569.proved))) (trans (cong refl Base.proved) (move-product MV01569.proved (MV01568.proved))))
