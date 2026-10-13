{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12350467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02416 as MV02416
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1235 • K0467 ≈ K0467 • K1235
proved = GL.•-cancelʳ {g = K1235 • K0467} {g' = K0467 • K1235} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV00676.proved (MV02416.proved))) (trans (cong refl Base.proved) (move-product MV02416.proved (MV00676.proved))))
