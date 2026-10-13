{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470126 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01685 as MV01685
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01686 as MV01686
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0126 ≈ K0126 • X47
proved = GL.•-cancelʳ {g = X47 • K0126} {g' = K0126 • X47} {h = p (s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01685.proved (MV01686.proved))) (trans (cong refl Base.proved) (move-product MV01686.proved (MV01685.proved))))
