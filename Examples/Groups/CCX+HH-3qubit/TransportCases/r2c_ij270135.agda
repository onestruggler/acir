{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270135 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01481 as MV01481
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01482 as MV01482
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K0135 ≈ K0135 • X27
proved = GL.•-cancelʳ {g = X27 • K0135} {g' = K0135 • X27} {h = p (s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01481.proved (MV01482.proved))) (trans (cong refl Base.proved) (move-product MV01482.proved (MV01481.proved))))
