{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0147 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02848 as MV02848
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02849 as MV02849
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X14 • K0147 ≈ M0 • K0147 • M0 • K0147 • M0
proved = GL.•-cancelʳ {g = X14 • K0147} {g' = M0 • K0147 • M0 • K0147 • M0} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02848.proved (MV00651.proved))) (trans (cong refl Base.proved) (move-product MV02849.proved (move-product MV00651.proved (move-product MV02849.proved (move-product MV00651.proved (MV02849.proved)))))))
