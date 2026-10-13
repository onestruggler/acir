{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02659 as MV02659
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02660 as MV02660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02661 as MV02661
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02662 as MV02662
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • K0347 ≈ K0347 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X03 • K0347} {g' = K0347 • X37 • M3 • M7} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02659.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV00667.proved (move-product MV02660.proved (move-product MV02661.proved (MV02662.proved))))))
