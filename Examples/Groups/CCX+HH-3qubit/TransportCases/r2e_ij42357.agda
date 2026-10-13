{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij42357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02167 as MV02167
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02168 as MV02168
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K2357 ≈ K2357 • M4
proved = GL.•-cancelʳ {g = M4 • K2357} {g' = K2357 • M4} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
  (trans (sym (move-product MV02167.proved (MV02168.proved))) (trans (cong refl Base.proved) (move-product MV02168.proved (MV02167.proved))))
