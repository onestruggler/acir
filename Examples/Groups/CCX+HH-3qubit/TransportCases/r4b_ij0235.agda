{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00656 as MV00656
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02857 as MV02857
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02858 as MV02858
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K0235 ≈ M0 • K0235 • M0 • K0235 • M0
proved = GL.•-cancelʳ {g = X23 • K0235} {g' = M0 • K0235 • M0 • K0235 • M0} {h = p (s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02857.proved (MV00656.proved))) (trans (cong refl Base.proved) (move-product MV02858.proved (move-product MV00656.proved (move-product MV02858.proved (move-product MV00656.proved (MV02858.proved)))))))
