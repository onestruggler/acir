{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02796 as MV02796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03023 as MV03023
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K2456 ≈ K2456 • X46
proved = GL.•-cancelʳ {g = X56 • K2456} {g' = K2456 • X46} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03023.proved (MV00701.proved))) (trans (cong refl Base.proved) (move-product MV00701.proved (MV02796.proved))))
