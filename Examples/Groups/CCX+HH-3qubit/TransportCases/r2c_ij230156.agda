{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01372 as MV01372
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K0156 ≈ K0156 • X23
proved = GL.•-cancelʳ {g = X23 • K0156} {g' = K0156 • X23} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01372.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (MV01372.proved))))
