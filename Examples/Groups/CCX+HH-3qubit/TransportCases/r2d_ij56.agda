{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij56 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01870 as MV01870
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01871 as MV01871
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • M6 ≈ M6 • M5
proved = GL.•-cancelʳ {g = M5 • M6} {g' = M6 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01870.proved (MV01871.proved))) (trans (cong refl Base.proved) (move-product MV01871.proved (MV01870.proved))))
