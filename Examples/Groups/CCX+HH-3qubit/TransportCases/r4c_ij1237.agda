{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1237 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00678 as MV00678
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02704 as MV02704
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03000 as MV03000
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • K1237 ≈ K1237 • X27
proved = GL.•-cancelʳ {g = X37 • K1237} {g' = K1237 • X27} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03000.proved (MV00678.proved))) (trans (cong refl Base.proved) (move-product MV00678.proved (MV02704.proved))))
