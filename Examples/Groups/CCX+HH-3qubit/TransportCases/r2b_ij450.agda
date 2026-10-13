{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij450 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00962 as MV00962
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00963 as MV00963
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • M0 ≈ M0 • X45
proved = GL.•-cancelʳ {g = X45 • M0} {g' = M0 • X45} {h = p (s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00962.proved (MV00963.proved))) (trans (cong refl Base.proved) (move-product MV00963.proved (MV00962.proved))))
