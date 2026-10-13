{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031247 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00681 as MV00681
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01071 as MV01071
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • K1247 ≈ K1247 • X03
proved = GL.•-cancelʳ {g = X03 • K1247} {g' = K1247 • X03} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01071.proved (MV00681.proved))) (trans (cong refl Base.proved) (move-product MV00681.proved (MV01071.proved))))
