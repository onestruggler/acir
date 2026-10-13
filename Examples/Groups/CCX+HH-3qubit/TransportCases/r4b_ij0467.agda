{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02891 as MV02891
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02892 as MV02892
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K0467 ≈ M0 • K0467 • M0 • K0467 • M0
proved = GL.•-cancelʳ {g = X46 • K0467} {g' = M0 • K0467 • M0 • K0467 • M0} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02891.proved (MV00673.proved))) (trans (cong refl Base.proved) (move-product MV02892.proved (move-product MV00673.proved (move-product MV02892.proved (move-product MV00673.proved (MV02892.proved)))))))
