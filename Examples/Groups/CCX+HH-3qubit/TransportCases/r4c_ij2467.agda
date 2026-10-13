{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00703 as MV00703
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02804 as MV02804
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03025 as MV03025
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K2467 ≈ K2467 • X47
proved = GL.•-cancelʳ {g = X67 • K2467} {g' = K2467 • X47} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03025.proved (MV00703.proved))) (trans (cong refl Base.proved) (move-product MV00703.proved (MV02804.proved))))
