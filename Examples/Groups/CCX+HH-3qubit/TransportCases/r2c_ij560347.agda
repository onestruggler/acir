{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01729 as MV01729
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01730 as MV01730
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0347 ≈ K0347 • X56
proved = GL.•-cancelʳ {g = X56 • K0347} {g' = K0347 • X56} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01729.proved (MV01730.proved))) (trans (cong refl Base.proved) (move-product MV01730.proved (MV01729.proved))))
