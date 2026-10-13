{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00695 as MV00695
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02772 as MV02772
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03017 as MV03017
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K2345 ≈ K2345 • X35
proved = GL.•-cancelʳ {g = X45 • K2345} {g' = K2345 • X35} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV03017.proved (MV00695.proved))) (trans (cong refl Base.proved) (move-product MV00695.proved (MV02772.proved))))
