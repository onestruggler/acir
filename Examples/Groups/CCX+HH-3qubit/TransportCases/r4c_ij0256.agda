{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0256 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02640 as MV02640
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02984 as MV02984
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X56 • K0256 ≈ K0256 • X26
proved = GL.•-cancelʳ {g = X56 • K0256} {g' = K0256 • X26} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02984.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV00662.proved (MV02640.proved))))
