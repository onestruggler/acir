{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij257 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00888 as MV00888
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00889 as MV00889
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X25 • M7 ≈ M7 • X25
proved = GL.•-cancelʳ {g = X25 • M7} {g' = M7 • X25} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00888.proved (MV00889.proved))) (trans (cong refl Base.proved) (move-product MV00889.proved (MV00888.proved))))
