{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij563 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01004 as MV01004
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01005 as MV01005
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • M3 ≈ M3 • X56
proved = GL.•-cancelʳ {g = X56 • M3} {g' = M3 • X56} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01004.proved (MV01005.proved))) (trans (cong refl Base.proved) (move-product MV01005.proved (MV01004.proved))))
