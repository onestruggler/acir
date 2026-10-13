{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij471356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01707 as MV01707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01708 as MV01708
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K1356 ≈ K1356 • X47
proved = GL.•-cancelʳ {g = X47 • K1356} {g' = K1356 • X47} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01707.proved (MV01708.proved))) (trans (cong refl Base.proved) (move-product MV01708.proved (MV01707.proved))))
