{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij124567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01796 as MV01796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03104 as MV03104
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03105 as MV03105
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03106 as MV03106
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1245 • K2567 ≈ K4567 • K1246
proved = GL.•-cancelʳ {g = K1245 • K2567} {g' = K4567 • K1246} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01796.proved (MV03104.proved))) (trans (cong refl Base.proved) (move-product MV03105.proved (MV03106.proved))))
