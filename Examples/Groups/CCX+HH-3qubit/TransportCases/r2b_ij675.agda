{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij675 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01032 as MV01032
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01033 as MV01033
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • M5 ≈ M5 • X67
proved = GL.•-cancelʳ {g = X67 • M5} {g' = M5 • X67} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01032.proved (MV01033.proved))) (trans (cong refl Base.proved) (move-product MV01033.proved (MV01032.proved))))
