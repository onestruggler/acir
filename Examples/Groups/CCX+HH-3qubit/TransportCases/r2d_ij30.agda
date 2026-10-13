{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij30 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01835 as MV01835
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01836 as MV01836
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • M0 ≈ M0 • M3
proved = GL.•-cancelʳ {g = M3 • M0} {g' = M0 • M3} {h = p (s2 • s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01835.proved (MV01836.proved))) (trans (cong refl Base.proved) (move-product MV01836.proved (MV01835.proved))))
