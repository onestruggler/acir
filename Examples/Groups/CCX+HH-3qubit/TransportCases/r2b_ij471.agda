{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij471 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00988 as MV00988
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00989 as MV00989
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • M1 ≈ M1 • X47
proved = GL.•-cancelʳ {g = X47 • M1} {g' = M1 • X47} {h = p (s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00988.proved (MV00989.proved))) (trans (cong refl Base.proved) (move-product MV00989.proved (MV00988.proved))))
