{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij041 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00737 as MV00737
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00738 as MV00738
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • M1 ≈ M1 • X04
proved = GL.•-cancelʳ {g = X04 • M1} {g' = M1 • X04} {h = p (s0 • s3 • s2)}
  (trans (sym (move-product MV00737.proved (MV00738.proved))) (trans (cong refl Base.proved) (move-product MV00738.proved (MV00737.proved))))
