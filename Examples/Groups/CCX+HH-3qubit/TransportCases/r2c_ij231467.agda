{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij231467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01387 as MV01387
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01388 as MV01388
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K1467 ≈ K1467 • X23
proved = GL.•-cancelʳ {g = X23 • K1467} {g' = K1467 • X23} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01387.proved (MV01388.proved))) (trans (cong refl Base.proved) (move-product MV01388.proved (MV01387.proved))))
