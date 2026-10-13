{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01339 as MV01339
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01340 as MV01340
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • K0234 ≈ K0234 • X17
proved = GL.•-cancelʳ {g = X17 • K0234} {g' = K0234 • X17} {h = p (s1 • s2 • s3 • s6 • s5)}
  (trans (sym (move-product MV01339.proved (MV01340.proved))) (trans (cong refl Base.proved) (move-product MV01340.proved (MV01339.proved))))
