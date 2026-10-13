{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270145 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01485 as MV01485
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01486 as MV01486
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K0145 ≈ K0145 • X27
proved = GL.•-cancelʳ {g = X27 • K0145} {g' = K0145 • X27} {h = p (s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01485.proved (MV01486.proved))) (trans (cong refl Base.proved) (move-product MV01486.proved (MV01485.proved))))
