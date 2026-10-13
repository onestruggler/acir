{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00707 as MV00707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02820 as MV02820
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03029 as MV03029
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K3467 ≈ K3467 • X47
proved = GL.•-cancelʳ {g = X67 • K3467} {g' = K3467 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03029.proved (MV00707.proved))) (trans (cong refl Base.proved) (move-product MV00707.proved (MV02820.proved))))
