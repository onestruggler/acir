{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01631 as MV01631
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01632 as MV01632
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0137 ≈ K0137 • X45
proved = GL.•-cancelʳ {g = X45 • K0137} {g' = K0137 • X45} {h = p (s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01631.proved (MV01632.proved))) (trans (cong refl Base.proved) (move-product MV01632.proved (MV01631.proved))))
