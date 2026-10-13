{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij674 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01030 as MV01030
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01031 as MV01031
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • M4 ≈ M4 • X67
proved = GL.•-cancelʳ {g = X67 • M4} {g' = M4 • X67} {h = p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01030.proved (MV01031.proved))) (trans (cong refl Base.proved) (move-product MV01031.proved (MV01030.proved))))
