{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01421 as MV01421
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01422 as MV01422
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • K0136 ≈ K0136 • X25
proved = GL.•-cancelʳ {g = X25 • K0136} {g' = K0136 • X25} {h = p (s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01421.proved (MV01422.proved))) (trans (cong refl Base.proved) (move-product MV01422.proved (MV01421.proved))))
