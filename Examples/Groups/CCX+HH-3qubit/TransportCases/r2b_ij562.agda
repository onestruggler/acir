{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij562 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01002 as MV01002
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01003 as MV01003
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • M2 ≈ M2 • X56
proved = GL.•-cancelʳ {g = X56 • M2} {g' = M2 • X56} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01002.proved (MV01003.proved))) (trans (cong refl Base.proved) (move-product MV01003.proved (MV01002.proved))))
