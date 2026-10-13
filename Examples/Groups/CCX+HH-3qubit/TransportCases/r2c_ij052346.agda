{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij052346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01139 as MV01139
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01140 as MV01140
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • K2346 ≈ K2346 • X05
proved = GL.•-cancelʳ {g = X05 • K2346} {g' = K2346 • X05} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01139.proved (MV01140.proved))) (trans (cong refl Base.proved) (move-product MV01140.proved (MV01139.proved))))
