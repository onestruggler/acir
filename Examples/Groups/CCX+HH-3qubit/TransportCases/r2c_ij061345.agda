{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01161 as MV01161
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01162 as MV01162
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • K1345 ≈ K1345 • X06
proved = GL.•-cancelʳ {g = X06 • K1345} {g' = K1345 • X06} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01161.proved (MV01162.proved))) (trans (cong refl Base.proved) (move-product MV01162.proved (MV01161.proved))))
