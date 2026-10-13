{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij73456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02379 as MV02379
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02380 as MV02380
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K3456 ≈ K3456 • M7
proved = GL.•-cancelʳ {g = M7 • K3456} {g' = K3456 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02379.proved (MV02380.proved))) (trans (cong refl Base.proved) (move-product MV02380.proved (MV02379.proved))))
