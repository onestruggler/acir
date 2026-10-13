{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij561 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01000 as MV01000
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01001 as MV01001
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • M1 ≈ M1 • X56
proved = GL.•-cancelʳ {g = X56 • M1} {g' = M1 • X56} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01000.proved (MV01001.proved))) (trans (cong refl Base.proved) (move-product MV01001.proved (MV01000.proved))))
