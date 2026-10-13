{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00696 as MV00696
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02775 as MV02775
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02776 as MV02776
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02777 as MV02777
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02778 as MV02778
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K2346 ≈ K2346 • X36 • M3 • M6
proved = GL.•-cancelʳ {g = X23 • K2346} {g' = K2346 • X36 • M3 • M6} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02775.proved (MV00696.proved))) (trans (cong refl Base.proved) (move-product MV00696.proved (move-product MV02776.proved (move-product MV02777.proved (MV02778.proved))))))
