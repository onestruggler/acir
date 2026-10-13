{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij3467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00707 as MV00707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02819 as MV02819
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02820 as MV02820
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02821 as MV02821
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02822 as MV02822
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K3467 ≈ K3467 • X47 • M4 • M7
proved = GL.•-cancelʳ {g = X34 • K3467} {g' = K3467 • X47 • M4 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02819.proved (MV00707.proved))) (trans (cong refl Base.proved) (move-product MV00707.proved (move-product MV02820.proved (move-product MV02821.proved (MV02822.proved))))))
