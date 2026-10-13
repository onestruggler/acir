{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02787 as MV02787
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02788 as MV02788
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02789 as MV02789
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02790 as MV02790
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K2357 ≈ K2357 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X23 • K2357} {g' = K2357 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02787.proved (MV00699.proved))) (trans (cong refl Base.proved) (move-product MV00699.proved (move-product MV02788.proved (move-product MV02789.proved (MV02790.proved))))))
