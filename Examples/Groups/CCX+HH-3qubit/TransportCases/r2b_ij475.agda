{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij475 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00994 as MV00994
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00995 as MV00995
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • M5 ≈ M5 • X47
proved = GL.•-cancelʳ {g = X47 • M5} {g' = M5 • X47} {h = p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00994.proved (MV00995.proved))) (trans (cong refl Base.proved) (move-product MV00995.proved (MV00994.proved))))
