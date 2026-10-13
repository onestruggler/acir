{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij023457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01754 as MV01754
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03077 as MV03077
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03078 as MV03078
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03079 as MV03079
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0234 • K2457 ≈ K3457 • K0235
proved = GL.•-cancelʳ {g = K0234 • K2457} {g' = K3457 • K0235} {h = p (s1 • s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01754.proved (MV03077.proved))) (trans (cong refl Base.proved) (move-product MV03078.proved (MV03079.proved))))
