{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02561347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02402 as MV02402
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0256 • K1347 ≈ K1347 • K0256
proved = GL.•-cancelʳ {g = K0256 • K1347} {g' = K1347 • K0256} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00662.proved (MV02402.proved))) (trans (cong refl Base.proved) (move-product MV02402.proved (MV00662.proved))))
