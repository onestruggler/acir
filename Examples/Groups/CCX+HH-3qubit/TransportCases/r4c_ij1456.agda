{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00691 as MV00691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02756 as MV02756
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03013 as MV03013
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K1456 ≈ K1456 • X46
proved = GL.•-cancelʳ {g = X56 • K1456} {g' = K1456 • X46} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03013.proved (MV00691.proved))) (trans (cong refl Base.proved) (move-product MV00691.proved (MV02756.proved))))
