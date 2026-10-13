{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00922 as MV00922
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00923 as MV00923
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • M6 ≈ M6 • X34
proved = GL.•-cancelʳ {g = X34 • M6} {g' = M6 • X34} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00922.proved (MV00923.proved))) (trans (cong refl Base.proved) (move-product MV00923.proved (MV00922.proved))))
