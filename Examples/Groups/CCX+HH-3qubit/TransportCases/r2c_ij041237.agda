{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01095 as MV01095
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K1237 ≈ K1237 • X04
proved = GL.•-cancelʳ {g = X04 • K1237} {g' = K1237 • X04} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01095.proved (MV00678.proved))) (trans (cong refl Base.proved) (move-product MV00678.proved (MV01095.proved))))
