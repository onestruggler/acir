{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02684 as MV02684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02995 as MV02995
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0467 ≈ K0467 • X47
proved = GL.•-cancelʳ {g = X67 • K0467} {g' = K0467 • X47} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02995.proved (MV00673.proved))) (trans (cong refl Base.proved) (move-product MV00673.proved (MV02684.proved))))
