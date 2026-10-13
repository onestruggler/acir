{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02788 as MV02788
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03021 as MV03021
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K2357 ≈ K2357 • X37
proved = GL.•-cancelʳ {g = X57 • K2357} {g' = K2357 • X37} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03021.proved (MV00699.proved))) (trans (cong refl Base.proved) (move-product MV00699.proved (MV02788.proved))))
