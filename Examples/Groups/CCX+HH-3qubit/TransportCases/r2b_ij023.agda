{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij023 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00715 as MV00715
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00716 as MV00716
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • M3 ≈ M3 • X02
proved = GL.•-cancelʳ {g = X02 • M3} {g' = M3 • X02} {h = p (s2 • s1 • s0 • s2)}
  (trans (sym (move-product MV00715.proved (MV00716.proved))) (trans (cong refl Base.proved) (move-product MV00716.proved (MV00715.proved))))
