{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij263457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01477 as MV01477
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01478 as MV01478
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X26 • K3457 ≈ K3457 • X26
proved = GL.•-cancelʳ {g = X26 • K3457} {g' = K3457 • X26} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01477.proved (MV01478.proved))) (trans (cong refl Base.proved) (move-product MV01478.proved (MV01477.proved))))
