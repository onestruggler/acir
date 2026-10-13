{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij271346 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01501 as MV01501
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01502 as MV01502
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K1346 ≈ K1346 • X27
proved = GL.•-cancelʳ {g = X27 • K1346} {g' = K1346 • X27} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01501.proved (MV01502.proved))) (trans (cong refl Base.proved) (move-product MV01502.proved (MV01501.proved))))
