{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij476 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00996 as MV00996
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00997 as MV00997
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • M6 ≈ M6 • X47
proved = GL.•-cancelʳ {g = X47 • M6} {g' = M6 • X47} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00996.proved (MV00997.proved))) (trans (cong refl Base.proved) (move-product MV00997.proved (MV00996.proved))))
