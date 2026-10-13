{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij175 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00850 as MV00850
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00851 as MV00851
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X17 • M5 ≈ M5 • X17
proved = GL.•-cancelʳ {g = X17 • M5} {g' = M5 • X17} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00850.proved (MV00851.proved))) (trans (cong refl Base.proved) (move-product MV00851.proved (MV00850.proved))))
