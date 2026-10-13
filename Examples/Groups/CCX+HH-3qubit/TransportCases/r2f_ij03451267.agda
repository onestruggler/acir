{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03451267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02405 as MV02405
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0345 • K1267 ≈ K1267 • K0345
proved = GL.•-cancelʳ {g = K0345 • K1267} {g' = K1267 • K0345} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00665.proved (MV02405.proved))) (trans (cong refl Base.proved) (move-product MV02405.proved (MV00665.proved))))
