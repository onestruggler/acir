{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij042356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01110 as MV01110
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01111 as MV01111
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X04 • K2356 ≈ K2356 • X04
proved = GL.•-cancelʳ {g = X04 • K2356} {g' = K2356 • X04} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01110.proved (MV01111.proved))) (trans (cong refl Base.proved) (move-product MV01111.proved (MV01110.proved))))
