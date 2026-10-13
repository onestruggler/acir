{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270356 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01495 as MV01495
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01496 as MV01496
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X27 • K0356 ≈ K0356 • X27
proved = GL.•-cancelʳ {g = X27 • K0356} {g' = K0356 • X27} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01495.proved (MV01496.proved))) (trans (cong refl Base.proved) (move-product MV01496.proved (MV01495.proved))))
