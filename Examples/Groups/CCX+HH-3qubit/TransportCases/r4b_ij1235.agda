{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1235 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00676 as MV00676
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02896 as MV02896
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02897 as MV02897
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K1235 ≈ M1 • K1235 • M1 • K1235 • M1
proved = GL.•-cancelʳ {g = X23 • K1235} {g' = M1 • K1235 • M1 • K1235 • M1} {h = p (s0 • s1 • s2 • s4 • s3)}
  (trans (sym (move-product MV02896.proved (MV00676.proved))) (trans (cong refl Base.proved) (move-product MV02897.proved (move-product MV00676.proved (move-product MV02897.proved (move-product MV00676.proved (MV02897.proved)))))))
