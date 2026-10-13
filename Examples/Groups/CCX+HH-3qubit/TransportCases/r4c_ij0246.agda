{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02632 as MV02632
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02982 as MV02982
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K0246 ≈ K0246 • X26
proved = GL.•-cancelʳ {g = X46 • K0246} {g' = K0246 • X26} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02982.proved (MV00660.proved))) (trans (cong refl Base.proved) (move-product MV00660.proved (MV02632.proved))))
