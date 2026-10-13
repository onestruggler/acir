{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0257 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02644 as MV02644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02985 as MV02985
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K0257 ≈ K0257 • X27
proved = GL.•-cancelʳ {g = X57 • K0257} {g' = K0257 • X27} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02985.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV00663.proved (MV02644.proved))))
