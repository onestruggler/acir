{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02619 as MV02619
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02620 as MV02620
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02621 as MV02621
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02622 as MV02622
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • K0236 ≈ K0236 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X02 • K0236} {g' = K0236 • X26 • M2 • M6} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02619.proved (MV00657.proved))) (trans (cong refl Base.proved) (move-product MV00657.proved (move-product MV02620.proved (move-product MV02621.proved (MV02622.proved))))))
