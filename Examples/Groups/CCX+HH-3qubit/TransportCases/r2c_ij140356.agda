{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij140356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01262 as MV01262
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01263 as MV01263
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X14 • K0356 ≈ K0356 • X14
proved = GL.•-cancelʳ {g = X14 • K0356} {g' = K0356 • X14} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01262.proved (MV01263.proved))) (trans (cong refl Base.proved) (move-product MV01263.proved (MV01262.proved))))
