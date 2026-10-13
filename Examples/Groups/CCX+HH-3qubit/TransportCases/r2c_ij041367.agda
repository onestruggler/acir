{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041367 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01106 as MV01106
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01107 as MV01107
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K1367 ≈ K1367 • X04
proved = GL.•-cancelʳ {g = X04 • K1367} {g' = K1367 • X04} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01106.proved (MV01107.proved))) (trans (cong refl Base.proved) (move-product MV01107.proved (MV01106.proved))))
