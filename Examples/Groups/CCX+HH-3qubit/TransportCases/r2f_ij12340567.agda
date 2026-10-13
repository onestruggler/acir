{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12340567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02415 as MV02415
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1234 • K0567 ≈ K0567 • K1234
proved = GL.•-cancelʳ {g = K1234 • K0567} {g' = K0567 • K1234} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV00675.proved (MV02415.proved))) (trans (cong refl Base.proved) (move-product MV02415.proved (MV00675.proved))))
