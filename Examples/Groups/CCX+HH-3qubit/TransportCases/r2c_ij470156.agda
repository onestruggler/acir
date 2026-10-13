{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470156 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01691 as MV01691
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01692 as MV01692
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X47 • K0156 ≈ K0156 • X47
proved = GL.•-cancelʳ {g = X47 • K0156} {g' = K0156 • X47} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01691.proved (MV01692.proved))) (trans (cong refl Base.proved) (move-product MV01692.proved (MV01691.proved))))
