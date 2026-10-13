{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02624 as MV02624
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02980 as MV02980
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • K0237 ≈ K0237 • X27
proved = GL.•-cancelʳ {g = X37 • K0237} {g' = K0237 • X27} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02980.proved (MV00658.proved))) (trans (cong refl Base.proved) (move-product MV00658.proved (MV02624.proved))))
