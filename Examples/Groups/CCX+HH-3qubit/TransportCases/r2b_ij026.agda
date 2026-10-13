{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij026 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00721 as MV00721
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00722 as MV00722
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • M6 ≈ M6 • X02
proved = GL.•-cancelʳ {g = X02 • M6} {g' = M6 • X02} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2)}
  (trans (sym (move-product MV00721.proved (MV00722.proved))) (trans (cong refl Base.proved) (move-product MV00722.proved (MV00721.proved))))
