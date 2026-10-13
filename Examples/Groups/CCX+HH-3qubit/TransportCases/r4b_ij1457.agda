{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij1457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00692 as MV00692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02928 as MV02928
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02929 as MV02929
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K1457 ≈ M1 • K1457 • M1 • K1457 • M1
proved = GL.•-cancelʳ {g = X45 • K1457} {g' = M1 • K1457 • M1 • K1457 • M1} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02928.proved (MV00692.proved))) (trans (cong refl Base.proved) (move-product MV02929.proved (move-product MV00692.proved (move-product MV02929.proved (move-product MV00692.proved (MV02929.proved)))))))
