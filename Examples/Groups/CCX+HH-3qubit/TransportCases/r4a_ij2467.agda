{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02803 as MV02803
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02804 as MV02804
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02805 as MV02805
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02806 as MV02806
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K2467 ≈ K2467 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X24 • K2467} {g' = K2467 • X47 • M4 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02803.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV00703.proved (move-product MV02804.proved (move-product MV02805.proved (MV02806.proved))))))
