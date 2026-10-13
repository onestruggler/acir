{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12560347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02422 as MV02422
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1256 • K0347 ≈ K0347 • K1256
proved = GL.•-cancelʳ {g = K1256 • K0347} {g' = K0347 • K1256} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00682.proved (MV02422.proved))) (trans (cong refl Base.proved) (move-product MV02422.proved (MV00682.proved))))
