{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0157 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02604 as MV02604
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02975 as MV02975
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K0157 ≈ K0157 • X17
proved = GL.•-cancelʳ {g = X57 • K0157} {g' = K0157 • X17} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02975.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV00653.proved (MV02604.proved))))
