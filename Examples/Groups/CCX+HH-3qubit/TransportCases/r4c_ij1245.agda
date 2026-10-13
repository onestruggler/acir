{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1245 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02708 as MV02708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03001 as MV03001
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K1245 ≈ K1245 • X25
proved = GL.•-cancelʳ {g = X45 • K1245} {g' = K1245 • X25} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV03001.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV00679.proved (MV02708.proved))))
