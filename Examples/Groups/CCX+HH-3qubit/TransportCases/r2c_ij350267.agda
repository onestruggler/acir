{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350267 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01550 as MV01550
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01551 as MV01551
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X35 • K0267 ≈ K0267 • X35
proved = GL.•-cancelʳ {g = X35 • K0267} {g' = K0267 • X35} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01550.proved (MV01551.proved))) (trans (cong refl Base.proved) (move-product MV01551.proved (MV01550.proved))))
