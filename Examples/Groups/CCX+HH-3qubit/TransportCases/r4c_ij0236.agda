{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02620 as MV02620
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02979 as MV02979
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X36 • K0236 ≈ K0236 • X26
proved = GL.•-cancelʳ {g = X36 • K0236} {g' = K0236 • X26} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02979.proved (MV00657.proved))) (trans (cong refl Base.proved) (move-product MV00657.proved (MV02620.proved))))
