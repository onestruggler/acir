{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02584 as MV02584
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02970 as MV02970
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X37 • K0137 ≈ K0137 • X17
proved = GL.•-cancelʳ {g = X37 • K0137} {g' = K0137 • X17} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02970.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (MV02584.proved))))
