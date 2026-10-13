{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij024 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00717 as MV00717
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00718 as MV00718
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • M4 ≈ M4 • X02
proved = GL.•-cancelʳ {g = X02 • M4} {g' = M4 • X02} {h = p (s3 • s2 • s1 • s0 • s2)}
  (trans (sym (move-product MV00717.proved (MV00718.proved))) (trans (cong refl Base.proved) (move-product MV00718.proved (MV00717.proved))))
