{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1457 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00692 as MV00692
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02760 as MV02760
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03014 as MV03014
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X57 • K1457 ≈ K1457 • X47
proved = GL.•-cancelʳ {g = X57 • K1457} {g' = K1457 • X47} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03014.proved (MV00692.proved))) (trans (cong refl Base.proved) (move-product MV00692.proved (MV02760.proved))))
