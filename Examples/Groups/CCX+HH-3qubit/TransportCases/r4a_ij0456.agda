{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02675 as MV02675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02676 as MV02676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02677 as MV02677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02678 as MV02678
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K0456 ≈ K0456 • X46 • M4 • M6
proved = GL.•-cancelʳ {g = X04 • K0456} {g' = K0456 • X46 • M4 • M6} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02675.proved (MV00671.proved))) (trans (cong refl Base.proved) (move-product MV00671.proved (move-product MV02676.proved (move-product MV02677.proved (MV02678.proved))))))
