{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij26 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01831 as MV01831
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01832 as MV01832
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • M6 ≈ M6 • M2
proved = GL.•-cancelʳ {g = M2 • M6} {g' = M6 • M2} {h = p (s1 • s0 • s5 • s4)}
  (trans (sym (move-product MV01831.proved (MV01832.proved))) (trans (cong refl Base.proved) (move-product MV01832.proved (MV01831.proved))))
