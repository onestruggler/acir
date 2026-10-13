{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij123467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01792 as MV01792
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03098 as MV03098
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03099 as MV03099
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03100 as MV03100
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1234 • K2467 ≈ K3467 • K1236
proved = GL.•-cancelʳ {g = K1234 • K2467} {g' = K3467 • K1236} {h = p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01792.proved (MV03098.proved))) (trans (cong refl Base.proved) (move-product MV03099.proved (MV03100.proved))))
