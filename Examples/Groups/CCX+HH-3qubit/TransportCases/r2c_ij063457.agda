{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij063457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01177 as MV01177
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01178 as MV01178
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X06 • K3457 ≈ K3457 • X06
proved = GL.•-cancelʳ {g = X06 • K3457} {g' = K3457 • X06} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01177.proved (MV01178.proved))) (trans (cong refl Base.proved) (move-product MV01178.proved (MV01177.proved))))
