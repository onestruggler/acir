{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230467 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01379 as MV01379
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01380 as MV01380
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K0467 ≈ K0467 • X23
proved = GL.•-cancelʳ {g = X23 • K0467} {g' = K0467 • X23} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01379.proved (MV01380.proved))) (trans (cong refl Base.proved) (move-product MV01380.proved (MV01379.proved))))
