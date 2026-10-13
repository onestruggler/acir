{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij160345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01321 as MV01321
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01322 as MV01322
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X16 • K0345 ≈ K0345 • X16
proved = GL.•-cancelʳ {g = X16 • K0345} {g' = K0345 • X16} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5)}
  (trans (sym (move-product MV01321.proved (MV01322.proved))) (trans (cong refl Base.proved) (move-product MV01322.proved (MV01321.proved))))
