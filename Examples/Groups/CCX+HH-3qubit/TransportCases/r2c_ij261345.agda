{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij261345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01469 as MV01469
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01470 as MV01470
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • K1345 ≈ K1345 • X26
proved = GL.•-cancelʳ {g = X26 • K1345} {g' = K1345 • X26} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01469.proved (MV01470.proved))) (trans (cong refl Base.proved) (move-product MV01470.proved (MV01469.proved))))
