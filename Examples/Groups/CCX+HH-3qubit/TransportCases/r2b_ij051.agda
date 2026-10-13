{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij051 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00749 as MV00749
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00750 as MV00750
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X05 • M1 ≈ M1 • X05
proved = GL.•-cancelʳ {g = X05 • M1} {g' = M1 • X05} {h = p (s0 • s4 • s3 • s2)}
  (trans (sym (move-product MV00749.proved (MV00750.proved))) (trans (cong refl Base.proved) (move-product MV00750.proved (MV00749.proved))))
