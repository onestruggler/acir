{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij31 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01837 as MV01837
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01838 as MV01838
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • M1 ≈ M1 • M3
proved = GL.•-cancelʳ {g = M3 • M1} {g' = M1 • M3} {h = p (s2 • s1 • s0 • s2 • s3)}
  (trans (sym (move-product MV01837.proved (MV01838.proved))) (trans (cong refl Base.proved) (move-product MV01838.proved (MV01837.proved))))
