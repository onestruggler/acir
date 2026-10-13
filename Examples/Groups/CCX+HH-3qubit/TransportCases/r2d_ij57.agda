{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij57 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01872 as MV01872
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01873 as MV01873
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M5 • M7 ≈ M7 • M5
proved = GL.•-cancelʳ {g = M5 • M7} {g' = M7 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01872.proved (MV01873.proved))) (trans (cong refl Base.proved) (move-product MV01873.proved (MV01872.proved))))
