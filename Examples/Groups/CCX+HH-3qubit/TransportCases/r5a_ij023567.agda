{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij023567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01786 as MV01786
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03083 as MV03083
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03084 as MV03084
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03085 as MV03085
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0235 • K2567 ≈ K3567 • K0236
proved = GL.•-cancelʳ {g = K0235 • K2567} {g' = K3567 • K0236} {h = p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01786.proved (MV03083.proved))) (trans (cong refl Base.proved) (move-product MV03084.proved (MV03085.proved))))
