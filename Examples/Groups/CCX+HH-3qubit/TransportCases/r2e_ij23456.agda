{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij23456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02032 as MV02032
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02033 as MV02033
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K3456 ≈ K3456 • M2
proved = GL.•-cancelʳ {g = M2 • K3456} {g' = K3456 • M2} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02032.proved (MV02033.proved))) (trans (cong refl Base.proved) (move-product MV02033.proved (MV02032.proved))))
