{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02004 as MV02004
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02005 as MV02005
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : M2 • K0456 ≈ K0456 • M2
proved = GL.•-cancelʳ {g = M2 • K0456} {g' = K0456 • M2} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV02004.proved (MV02005.proved))) (trans (cong refl Base.proved) (move-product MV02005.proved (MV02004.proved))))
