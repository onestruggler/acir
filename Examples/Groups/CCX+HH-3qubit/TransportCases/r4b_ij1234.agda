{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1234 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00675 as MV00675
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01810 as MV01810
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02895 as MV02895
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K1234 ≈ M1 • K1234 • M1 • K1234 • M1
proved = GL.•-cancelʳ {g = X23 • K1234} {g' = M1 • K1234 • M1 • K1234 • M1} {h = p (s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV02895.proved (MV00675.proved))) (trans (cong refl Base.proved) (move-product MV01810.proved (move-product MV00675.proved (move-product MV01810.proved (move-product MV00675.proved (MV01810.proved)))))))
