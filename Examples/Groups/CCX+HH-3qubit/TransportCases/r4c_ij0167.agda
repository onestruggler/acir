{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0167 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02608 as MV02608
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02976 as MV02976
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0167 ≈ K0167 • X17
proved = GL.•-cancelʳ {g = X67 • K0167} {g' = K0167 • X17} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02976.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV00654.proved (MV02608.proved))))
