{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij351 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00928 as MV00928
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00929 as MV00929
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • M1 ≈ M1 • X35
proved = GL.•-cancelʳ {g = X35 • M1} {g' = M1 • X35} {h = p (s0 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00928.proved (MV00929.proved))) (trans (cong refl Base.proved) (move-product MV00929.proved (MV00928.proved))))
