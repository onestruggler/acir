{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0246 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02865 as MV02865
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02866 as MV02866
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K0246 ≈ M0 • K0246 • M0 • K0246 • M0
proved = GL.•-cancelʳ {g = X24 • K0246} {g' = M0 • K0246 • M0 • K0246 • M0} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02865.proved (MV00660.proved))) (trans (cong refl Base.proved) (move-product MV02866.proved (move-product MV00660.proved (move-product MV02866.proved (move-product MV00660.proved (MV02866.proved)))))))
