{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02795 as MV02795
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02796 as MV02796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02797 as MV02797
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02798 as MV02798
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X24 • K2456 ≈ K2456 • X46 • M4 • M6
proved = GL.•-cancelʳ {g = X24 • K2456} {g' = K2456 • X46 • M4 • M6} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02795.proved (MV00701.proved))) (trans (cong refl Base.proved) (move-product MV00701.proved (move-product MV02796.proved (move-product MV02797.proved (MV02798.proved))))))
