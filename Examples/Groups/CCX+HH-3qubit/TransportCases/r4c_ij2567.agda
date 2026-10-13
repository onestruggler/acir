{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00704 as MV00704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02808 as MV02808
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03026 as MV03026
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K2567 ≈ K2567 • X57
proved = GL.•-cancelʳ {g = X67 • K2567} {g' = K2567 • X57} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03026.proved (MV00704.proved))) (trans (cong refl Base.proved) (move-product MV00704.proved (MV02808.proved))))
