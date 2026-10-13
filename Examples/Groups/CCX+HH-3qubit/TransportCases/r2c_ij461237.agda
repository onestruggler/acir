{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij461237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01673 as MV01673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01674 as MV01674
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X46 • K1237 ≈ K1237 • X46
proved = GL.•-cancelʳ {g = X46 • K1237} {g' = K1237 • X46} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01673.proved (MV01674.proved))) (trans (cong refl Base.proved) (move-product MV01674.proved (MV01673.proved))))
