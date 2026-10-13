{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00671 as MV00671
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02676 as MV02676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02993 as MV02993
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0456 ≈ K0456 • X46
proved = GL.•-cancelʳ {g = X56 • K0456} {g' = K0456 • X46} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02993.proved (MV00671.proved))) (trans (cong refl Base.proved) (move-product MV00671.proved (MV02676.proved))))
