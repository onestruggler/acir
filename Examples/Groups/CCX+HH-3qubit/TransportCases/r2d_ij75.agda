{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij75 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01896 as MV01896
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01897 as MV01897
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • M5 ≈ M5 • M7
proved = GL.•-cancelʳ {g = M7 • M5} {g' = M5 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01896.proved (MV01897.proved))) (trans (cong refl Base.proved) (move-product MV01897.proved (MV01896.proved))))
