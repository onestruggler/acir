{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij043 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00741 as MV00741
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00742 as MV00742
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • M3 ≈ M3 • X04
proved = GL.•-cancelʳ {g = X04 • M3} {g' = M3 • X04} {h = p (s2 • s1 • s0 • s3 • s2)}
  (trans (sym (move-product MV00741.proved (MV00742.proved))) (trans (cong refl Base.proved) (move-product MV00742.proved (MV00741.proved))))
