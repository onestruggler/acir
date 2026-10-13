{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00669 as MV00669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02667 as MV02667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02668 as MV02668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02669 as MV02669
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02670 as MV02670
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • K0357 ≈ K0357 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X03 • K0357} {g' = K0357 • X37 • M3 • M7} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02667.proved (MV00669.proved))) (trans (cong refl Base.proved) (move-product MV00669.proved (move-product MV02668.proved (move-product MV02669.proved (MV02670.proved))))))
