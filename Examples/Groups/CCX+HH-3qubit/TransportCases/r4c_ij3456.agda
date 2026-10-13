{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00705 as MV00705
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02812 as MV02812
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03027 as MV03027
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K3456 ≈ K3456 • X46
proved = GL.•-cancelʳ {g = X56 • K3456} {g' = K3456 • X46} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03027.proved (MV00705.proved))) (trans (cong refl Base.proved) (move-product MV00705.proved (MV02812.proved))))
