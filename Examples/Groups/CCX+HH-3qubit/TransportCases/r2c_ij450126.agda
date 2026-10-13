{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01625 as MV01625
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01626 as MV01626
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0126 ≈ K0126 • X45
proved = GL.•-cancelʳ {g = X45 • K0126} {g' = K0126 • X45} {h = p (s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01625.proved (MV01626.proved))) (trans (cong refl Base.proved) (move-product MV01626.proved (MV01625.proved))))
