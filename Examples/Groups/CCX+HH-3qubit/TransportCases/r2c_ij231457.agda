{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij231457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01385 as MV01385
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01386 as MV01386
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X23 • K1457 ≈ K1457 • X23
proved = GL.•-cancelʳ {g = X23 • K1457} {g' = K1457 • X23} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01385.proved (MV01386.proved))) (trans (cong refl Base.proved) (move-product MV01386.proved (MV01385.proved))))
