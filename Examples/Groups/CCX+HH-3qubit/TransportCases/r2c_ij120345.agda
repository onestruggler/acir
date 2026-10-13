{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01209 as MV01209
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K0345 ≈ K0345 • X12
proved = GL.•-cancelʳ {g = X12 • K0345} {g' = K0345 • X12} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01209.proved (MV00665.proved))) (trans (cong refl Base.proved) (move-product MV00665.proved (MV01209.proved))))
