{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij24560137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00701 as MV00701
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02441 as MV02441
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : K2456 • K0137 ≈ K0137 • K2456
proved = GL.•-cancelʳ {g = K2456 • K0137} {g' = K0137 • K2456} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00701.proved (MV02441.proved))) (trans (cong refl Base.proved) (move-product MV02441.proved (MV00701.proved))))
