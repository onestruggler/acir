{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij234567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01800 as MV01800
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03110 as MV03110
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03111 as MV03111
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03112 as MV03112
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K2345 • K3567 ≈ K4567 • K2346
proved = GL.•-cancelʳ {g = K2345 • K3567} {g' = K4567 • K2346} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01800.proved (MV03110.proved))) (trans (cong refl Base.proved) (move-product MV03111.proved (MV03112.proved))))
