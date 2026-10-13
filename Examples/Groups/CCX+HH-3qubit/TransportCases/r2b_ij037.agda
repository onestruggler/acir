{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij037 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00735 as MV00735
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00736 as MV00736
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X03 • M7 ≈ M7 • X03
proved = GL.•-cancelʳ {g = X03 • M7} {g' = M7 • X03} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)}
  (trans (sym (move-product MV00735.proved (MV00736.proved))) (trans (cong refl Base.proved) (move-product MV00736.proved (MV00735.proved))))
