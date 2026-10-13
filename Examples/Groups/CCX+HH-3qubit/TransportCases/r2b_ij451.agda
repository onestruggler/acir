{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij451 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00964 as MV00964
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00965 as MV00965
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • M1 ≈ M1 • X45
proved = GL.•-cancelʳ {g = X45 • M1} {g' = M1 • X45} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2)}
  (trans (sym (move-product MV00964.proved (MV00965.proved))) (trans (cong refl Base.proved) (move-product MV00965.proved (MV00964.proved))))
