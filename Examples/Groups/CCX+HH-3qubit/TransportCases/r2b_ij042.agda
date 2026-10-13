{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij042 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00739 as MV00739
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00740 as MV00740
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • M2 ≈ M2 • X04
proved = GL.•-cancelʳ {g = X04 • M2} {g' = M2 • X04} {h = p (s1 • s0 • s3 • s2)}
  (trans (sym (move-product MV00739.proved (MV00740.proved))) (trans (cong refl Base.proved) (move-product MV00740.proved (MV00739.proved))))
