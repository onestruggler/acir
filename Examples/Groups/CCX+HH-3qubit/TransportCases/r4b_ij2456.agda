{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij2456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02946 as MV02946
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02947 as MV02947
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K2456 ≈ M2 • K2456 • M2 • K2456 • M2
proved = GL.•-cancelʳ {g = X45 • K2456} {g' = M2 • K2456 • M2 • K2456 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02946.proved (MV00701.proved))) (trans (cong refl Base.proved) (move-product MV02947.proved (move-product MV00701.proved (move-product MV02947.proved (move-product MV00701.proved (MV02947.proved)))))))
