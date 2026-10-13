{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02731 as MV02731
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02732 as MV02732
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02733 as MV02733
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02734 as MV02734
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X13 • K1345 ≈ K1345 • X35 • M3 • M5
proved = GL.•-cancelʳ {g = X13 • K1345} {g' = K1345 • X35 • M3 • M5} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02731.proved (MV00685.proved))) (trans (cong refl Base.proved) (move-product MV00685.proved (move-product MV02732.proved (move-product MV02733.proved (MV02734.proved))))))
