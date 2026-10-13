{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0147 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00651 as MV00651
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02596 as MV02596
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02973 as MV02973
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0147 ≈ K0147 • X17
proved = GL.•-cancelʳ {g = X47 • K0147} {g' = K0147 • X17} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02973.proved (MV00651.proved))) (trans (cong refl Base.proved) (move-product MV00651.proved (MV02596.proved))))
