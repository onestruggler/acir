{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01291 as MV01291
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01292 as MV01292
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K0346 ≈ K0346 • X15
proved = GL.•-cancelʳ {g = X15 • K0346} {g' = K0346 • X15} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01291.proved (MV01292.proved))) (trans (cong refl Base.proved) (move-product MV01292.proved (MV01291.proved))))
