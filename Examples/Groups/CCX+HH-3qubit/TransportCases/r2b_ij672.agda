{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij672 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01026 as MV01026
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01027 as MV01027
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • M2 ≈ M2 • X67
proved = GL.•-cancelʳ {g = X67 • M2} {g' = M2 • X67} {h = p (s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01026.proved (MV01027.proved))) (trans (cong refl Base.proved) (move-product MV01027.proved (MV01026.proved))))
