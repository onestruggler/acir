{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270456 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01497 as MV01497
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01498 as MV01498
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K0456 ≈ K0456 • X27
proved = GL.•-cancelʳ {g = X27 • K0456} {g' = K0456 • X27} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01497.proved (MV01498.proved))) (trans (cong refl Base.proved) (move-product MV01498.proved (MV01497.proved))))
