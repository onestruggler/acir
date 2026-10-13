{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij134567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01798 as MV01798
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03107 as MV03107
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03108 as MV03108
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03109 as MV03109
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K1345 • K3567 ≈ K4567 • K1346
proved = GL.•-cancelʳ {g = K1345 • K3567} {g' = K4567 • K1346} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01798.proved (MV03107.proved))) (trans (cong refl Base.proved) (move-product MV03108.proved (MV03109.proved))))
