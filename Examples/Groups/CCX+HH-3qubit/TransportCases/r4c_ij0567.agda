{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02688 as MV02688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02996 as MV02996
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0567 ≈ K0567 • X57
proved = GL.•-cancelʳ {g = X67 • K0567} {g' = K0567 • X57} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02996.proved (MV00674.proved))) (trans (cong refl Base.proved) (move-product MV00674.proved (MV02688.proved))))
