{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02744 as MV02744
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03010 as MV03010
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K1356 ≈ K1356 • X36
proved = GL.•-cancelʳ {g = X56 • K1356} {g' = K1356 • X36} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03010.proved (MV00688.proved))) (trans (cong refl Base.proved) (move-product MV00688.proved (MV02744.proved))))
