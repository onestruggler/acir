{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01629 as MV01629
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01630 as MV01630
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

import Presentation.GroupLike as GLib
open import Examples.Groups.CCX+HH-3qubit.GroupLike using (grouplike)
module GL = GLib.Group-Lemmas _===_ grouplike

proved : X45 • K0136 ≈ K0136 • X45
proved = GL.•-cancelʳ {g = X45 • K0136} {g' = K0136 • X45} {h = p (s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01629.proved (MV01630.proved))) (trans (cong refl Base.proved) (move-product MV01630.proved (MV01629.proved))))
