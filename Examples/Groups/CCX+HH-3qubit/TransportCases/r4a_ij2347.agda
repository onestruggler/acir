{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00697 as MV00697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02779 as MV02779
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02780 as MV02780
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02781 as MV02781
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02782 as MV02782
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K2347 ≈ K2347 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X23 • K2347} {g' = K2347 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02779.proved (MV00697.proved))) (trans (cong refl Base.proved) (move-product MV00697.proved (move-product MV02780.proved (move-product MV02781.proved (MV02782.proved))))))
