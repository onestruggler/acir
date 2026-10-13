{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij2347 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00697 as MV00697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02780 as MV02780
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03019 as MV03019
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K2347 ≈ K2347 • X37
proved = GL.•-cancelʳ {g = X47 • K2347} {g' = K2347 • X37} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03019.proved (MV00697.proved))) (trans (cong refl Base.proved) (move-product MV00697.proved (MV02780.proved))))
