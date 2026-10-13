{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00655 as MV00655
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01801 as MV01801
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02856 as MV02856
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K0234 ≈ M0 • K0234 • M0 • K0234 • M0
proved = GL.•-cancelʳ {g = X23 • K0234} {g' = M0 • K0234 • M0 • K0234 • M0} {h = p (s1 • s2 • s3)}
  (trans (sym (move-product MV02856.proved (MV00655.proved))) (trans (cong refl Base.proved) (move-product MV01801.proved (move-product MV00655.proved (move-product MV01801.proved (move-product MV00655.proved (MV01801.proved)))))))
