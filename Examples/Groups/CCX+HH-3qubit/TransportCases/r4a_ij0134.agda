{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02571 as MV02571
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02572 as MV02572
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02573 as MV02573
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02574 as MV02574
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • K0134 ≈ K0134 • X14 • M1 • M4
proved = GL.•-cancelʳ {g = X01 • K0134} {g' = K0134 • X14 • M1 • M4} {h = p (s2 • s3)}
  (trans (sym (move-product MV02571.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV00645.proved (move-product MV02572.proved (move-product MV02573.proved (MV02574.proved))))))
