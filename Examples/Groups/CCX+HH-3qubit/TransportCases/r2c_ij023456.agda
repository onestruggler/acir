{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij023456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01059 as MV01059
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01060 as MV01060
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X02 • K3456 ≈ K3456 • X02
proved = GL.•-cancelʳ {g = X02 • K3456} {g' = K3456 • X02} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01059.proved (MV01060.proved))) (trans (cong refl Base.proved) (move-product MV01060.proved (MV01059.proved))))
