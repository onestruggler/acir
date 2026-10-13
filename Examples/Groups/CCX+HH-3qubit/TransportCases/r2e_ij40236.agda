{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij40236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02127 as MV02127
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02128 as MV02128
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M4 • K0236 ≈ K0236 • M4
proved = GL.•-cancelʳ {g = M4 • K0236} {g' = K0236 • M4} {h = p (s1 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02127.proved (MV02128.proved))) (trans (cong refl Base.proved) (move-product MV02128.proved (MV02127.proved))))
