{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij034567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01790 as MV01790
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03089 as MV03089
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03090 as MV03090
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03091 as MV03091
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0345 • K3567 ≈ K4567 • K0346
proved = GL.•-cancelʳ {g = K0345 • K3567} {g' = K4567 • K0346} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01790.proved (MV03089.proved))) (trans (cong refl Base.proved) (move-product MV03090.proved (MV03091.proved))))
