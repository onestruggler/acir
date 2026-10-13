{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij671 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01024 as MV01024
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01025 as MV01025
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • M1 ≈ M1 • X67
proved = GL.•-cancelʳ {g = X67 • M1} {g' = M1 • X67} {h = p (s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01024.proved (MV01025.proved))) (trans (cong refl Base.proved) (move-product MV01025.proved (MV01024.proved))))
