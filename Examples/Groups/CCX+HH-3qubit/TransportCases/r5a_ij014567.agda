{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij014567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01782 as MV01782
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03071 as MV03071
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03072 as MV03072
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03073 as MV03073
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0145 • K1567 ≈ K4567 • K0146
proved = GL.•-cancelʳ {g = K0145 • K1567} {g' = K4567 • K0146} {h = p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01782.proved (MV03071.proved))) (trans (cong refl Base.proved) (move-product MV03072.proved (MV03073.proved))))
