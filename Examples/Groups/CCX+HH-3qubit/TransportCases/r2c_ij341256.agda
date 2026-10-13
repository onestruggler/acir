{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij341256 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01526 as MV01526
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01527 as MV01527
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X34 • K1256 ≈ K1256 • X34
proved = GL.•-cancelʳ {g = X34 • K1256} {g' = K1256 • X34} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01526.proved (MV01527.proved))) (trans (cong refl Base.proved) (move-product MV01527.proved (MV01526.proved))))
