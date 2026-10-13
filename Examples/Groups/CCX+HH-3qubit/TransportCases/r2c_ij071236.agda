{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01183 as MV01183
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01184 as MV01184
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X07 • K1236 ≈ K1236 • X07
proved = GL.•-cancelʳ {g = X07 • K1236} {g' = K1236 • X07} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01183.proved (MV01184.proved))) (trans (cong refl Base.proved) (move-product MV01184.proved (MV01183.proved))))
