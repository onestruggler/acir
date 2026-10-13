{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01187 as MV01187
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01188 as MV01188
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K1246 ≈ K1246 • X07
proved = GL.•-cancelʳ {g = X07 • K1246} {g' = K1246 • X07} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01187.proved (MV01188.proved))) (trans (cong refl Base.proved) (move-product MV01188.proved (MV01187.proved))))
