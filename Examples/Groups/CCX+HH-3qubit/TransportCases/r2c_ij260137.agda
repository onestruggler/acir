{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260137 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01453 as MV01453
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01454 as MV01454
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • K0137 ≈ K0137 • X26
proved = GL.•-cancelʳ {g = X26 • K0137} {g' = K0137 • X26} {h = p (s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01453.proved (MV01454.proved))) (trans (cong refl Base.proved) (move-product MV01454.proved (MV01453.proved))))
