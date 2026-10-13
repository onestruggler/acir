{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij70234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02331 as MV02331
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02332 as MV02332
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M7 • K0234 ≈ K0234 • M7
proved = GL.•-cancelʳ {g = M7 • K0234} {g' = K0234 • M7} {h = p (s1 • s2 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02331.proved (MV02332.proved))) (trans (cong refl Base.proved) (move-product MV02332.proved (MV02331.proved))))
