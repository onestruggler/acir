{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02461357 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02400 as MV02400
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0246 • K1357 ≈ K1357 • K0246
proved = GL.•-cancelʳ {g = K0246 • K1357} {g' = K1357 • K0246} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00660.proved (MV02400.proved))) (trans (cong refl Base.proved) (move-product MV02400.proved (MV00660.proved))))
