{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij014 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00637 as MV00637
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00711 as MV00711
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X01 • M4 ≈ M4 • X01
proved = GL.•-cancelʳ {g = X01 • M4} {g' = M4 • X01} {h = p (s3 • s2 • s1 • s0)}
  (trans (sym (move-product MV00711.proved (MV00637.proved))) (trans (cong refl Base.proved) (move-product MV00637.proved (MV00711.proved))))
