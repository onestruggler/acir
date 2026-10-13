{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij023456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01724 as MV01724
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03074 as MV03074
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03075 as MV03075
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03076 as MV03076
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0234 • K2456 ≈ K3456 • K0235
proved = GL.•-cancelʳ {g = K0234 • K2456} {g' = K3456 • K0235} {h = p (s1 • s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01724.proved (MV03074.proved))) (trans (cong refl Base.proved) (move-product MV03075.proved (MV03076.proved))))
