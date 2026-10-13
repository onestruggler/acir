{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00247 as MV00247
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00252 as MV00252
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00500 as MV00500
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00557 as MV00557
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K0123 • K1346 ≈ K2346 • K0124
proved = GL.•-cancelʳ {g = K0123 • K1346} {g' = K2346 • K0124} {h = p (s5)}
  (trans (sym (move-product MV00247.proved (MV00500.proved))) (trans (cong refl Base.proved) (move-product MV00557.proved (MV00252.proved))))
