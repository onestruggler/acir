{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00685 as MV00685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02732 as MV02732
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03007 as MV03007
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K1345 ≈ K1345 • X35
proved = GL.•-cancelʳ {g = X45 • K1345} {g' = K1345 • X35} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV03007.proved (MV00685.proved))) (trans (cong refl Base.proved) (move-product MV00685.proved (MV02732.proved))))
