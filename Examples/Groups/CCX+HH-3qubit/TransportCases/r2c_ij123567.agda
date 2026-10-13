{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij123567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01225 as MV01225
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01226 as MV01226
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X12 • K3567 ≈ K3567 • X12
proved = GL.•-cancelʳ {g = X12 • K3567} {g' = K3567 • X12} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01225.proved (MV01226.proved))) (trans (cong refl Base.proved) (move-product MV01226.proved (MV01225.proved))))
