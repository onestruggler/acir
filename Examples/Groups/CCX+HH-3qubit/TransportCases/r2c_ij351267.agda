{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij351267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01558 as MV01558
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01559 as MV01559
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K1267 ≈ K1267 • X35
proved = GL.•-cancelʳ {g = X35 • K1267} {g' = K1267 • X35} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01558.proved (MV01559.proved))) (trans (cong refl Base.proved) (move-product MV01559.proved (MV01558.proved))))
