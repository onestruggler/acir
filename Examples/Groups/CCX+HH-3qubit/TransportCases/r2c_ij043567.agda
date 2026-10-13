{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij043567 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01118 as MV01118
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01119 as MV01119
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K3567 ≈ K3567 • X04
proved = GL.•-cancelʳ {g = X04 • K3567} {g' = K3567 • X04} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01118.proved (MV01119.proved))) (trans (cong refl Base.proved) (move-product MV01119.proved (MV01118.proved))))
