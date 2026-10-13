{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01775 as MV01775
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01776 as MV01776
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X67 • K0125 ≈ K0125 • X67
proved = GL.•-cancelʳ {g = X67 • K0125} {g' = K0125 • X67} {h = p (s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01775.proved (MV01776.proved))) (trans (cong refl Base.proved) (move-product MV01776.proved (MV01775.proved))))
