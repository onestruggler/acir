{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00668 as MV00668
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02664 as MV02664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02990 as MV02990
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0356 ≈ K0356 • X36
proved = GL.•-cancelʳ {g = X56 • K0356} {g' = K0356 • X36} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02990.proved (MV00668.proved))) (trans (cong refl Base.proved) (move-product MV00668.proved (MV02664.proved))))
