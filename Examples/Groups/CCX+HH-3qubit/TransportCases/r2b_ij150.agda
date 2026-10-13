{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij150 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00818 as MV00818
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00819 as MV00819
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X15 • M0 ≈ M0 • X15
proved = GL.•-cancelʳ {g = X15 • M0} {g' = M0 • X15} {h = p (s4 • s3 • s2)}
  (trans (sym (move-product MV00818.proved (MV00819.proved))) (trans (cong refl Base.proved) (move-product MV00819.proved (MV00818.proved))))
