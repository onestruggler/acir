{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij73 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00640 as MV00640
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01893 as MV01893
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • M3 ≈ M3 • M7
proved = GL.•-cancelʳ {g = M7 • M3} {g' = M3 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00640.proved (MV01893.proved))) (trans (cong refl Base.proved) (move-product MV01893.proved (MV00640.proved))))
