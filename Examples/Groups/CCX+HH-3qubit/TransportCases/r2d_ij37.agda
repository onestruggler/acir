{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij37 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01846 as MV01846
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01847 as MV01847
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M3 • M7 ≈ M7 • M3
proved = GL.•-cancelʳ {g = M3 • M7} {g' = M7 • M3} {h = p (s2 • s1 • s0 • s6 • s5 • s4)}
  (trans (sym (move-product MV01846.proved (MV01847.proved))) (trans (cong refl Base.proved) (move-product MV01847.proved (MV01846.proved))))
