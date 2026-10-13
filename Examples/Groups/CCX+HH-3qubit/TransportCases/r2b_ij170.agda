{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij170 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00842 as MV00842
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00843 as MV00843
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • M0 ≈ M0 • X17
proved = GL.•-cancelʳ {g = X17 • M0} {g' = M0 • X17} {h = p (s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00842.proved (MV00843.proved))) (trans (cong refl Base.proved) (move-product MV00843.proved (MV00842.proved))))
