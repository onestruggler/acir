{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01283 as MV01283
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01284 as MV01284
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • K0237 ≈ K0237 • X15
proved = GL.•-cancelʳ {g = X15 • K0237} {g' = K0237 • X15} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01283.proved (MV01284.proved))) (trans (cong refl Base.proved) (move-product MV01284.proved (MV01283.proved))))
