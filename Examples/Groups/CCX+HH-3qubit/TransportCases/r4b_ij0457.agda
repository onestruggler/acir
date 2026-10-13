{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00672 as MV00672
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02889 as MV02889
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02890 as MV02890
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0457 ≈ M0 • K0457 • M0 • K0457 • M0
proved = GL.•-cancelʳ {g = X45 • K0457} {g' = M0 • K0457 • M0 • K0457 • M0} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02889.proved (MV00672.proved))) (trans (cong refl Base.proved) (move-product MV02890.proved (move-product MV00672.proved (move-product MV02890.proved (move-product MV00672.proved (MV02890.proved)))))))
