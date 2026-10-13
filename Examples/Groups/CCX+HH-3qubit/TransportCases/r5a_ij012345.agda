{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03032 as MV03032
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03033 as MV03033
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03034 as MV03034
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0123 • K1345 ≈ K2345 • K0124
proved = GL.•-cancelʳ {g = K0123 • K1345} {g' = K2345 • K0124} {h = p (ε)}
  (trans (sym (move-product MV00641.proved (MV03032.proved))) (trans (cong refl Base.proved) (move-product MV03033.proved (MV03034.proved))))
