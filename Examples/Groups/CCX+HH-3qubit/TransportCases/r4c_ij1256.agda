{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1256 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02720 as MV02720
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03004 as MV03004
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K1256 ≈ K1256 • X26
proved = GL.•-cancelʳ {g = X56 • K1256} {g' = K1256 • X26} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03004.proved (MV00682.proved))) (trans (cong refl Base.proved) (move-product MV00682.proved (MV02720.proved))))
