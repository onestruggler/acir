{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01069 as MV01069
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • K1245 ≈ K1245 • X03
proved = GL.•-cancelʳ {g = X03 • K1245} {g' = K1245 • X03} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01069.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV00679.proved (MV01069.proved))))
