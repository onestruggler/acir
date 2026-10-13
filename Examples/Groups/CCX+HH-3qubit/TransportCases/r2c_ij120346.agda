{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij120346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01210 as MV01210
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K0346 ≈ K0346 • X12
proved = GL.•-cancelʳ {g = X12 • K0346} {g' = K0346 • X12} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01210.proved (MV00666.proved))) (trans (cong refl Base.proved) (move-product MV00666.proved (MV01210.proved))))
