{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij451236 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01643 as MV01643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01644 as MV01644
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K1236 ≈ K1236 • X45
proved = GL.•-cancelʳ {g = X45 • K1236} {g' = K1236 • X45} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01643.proved (MV01644.proved))) (trans (cong refl Base.proved) (move-product MV01644.proved (MV01643.proved))))
