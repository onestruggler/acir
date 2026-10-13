{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij021 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as MV00000
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00104 as MV00104
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • M1 ≈ M1 • X02
proved = GL.•-cancelʳ {g = X02 • M1} {g' = M1 • X02} {h = p (s0)}
  (trans (sym (move-product MV00104.proved (MV00000.proved))) (trans (cong refl Base.proved) (move-product MV00000.proved (MV00104.proved))))
