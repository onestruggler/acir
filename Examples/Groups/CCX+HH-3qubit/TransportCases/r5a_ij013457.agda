{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij013457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01748 as MV01748
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03062 as MV03062
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03063 as MV03063
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03064 as MV03064
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0134 • K1457 ≈ K3457 • K0135
proved = GL.•-cancelʳ {g = K0134 • K1457} {g' = K3457 • K0135} {h = p (s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01748.proved (MV03062.proved))) (trans (cong refl Base.proved) (move-product MV03063.proved (MV03064.proved))))
