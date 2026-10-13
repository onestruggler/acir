{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01683 as MV01683
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01684 as MV01684
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0125 ≈ K0125 • X47
proved = GL.•-cancelʳ {g = X47 • K0125} {g' = K0125 • X47} {h = p (s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01683.proved (MV01684.proved))) (trans (cong refl Base.proved) (move-product MV01684.proved (MV01683.proved))))
