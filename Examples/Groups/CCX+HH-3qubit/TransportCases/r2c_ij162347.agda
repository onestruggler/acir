{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij162347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01331 as MV01331
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01332 as MV01332
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K2347 ≈ K2347 • X16
proved = GL.•-cancelʳ {g = X16 • K2347} {g' = K2347 • X16} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01331.proved (MV01332.proved))) (trans (cong refl Base.proved) (move-product MV01332.proved (MV01331.proved))))
