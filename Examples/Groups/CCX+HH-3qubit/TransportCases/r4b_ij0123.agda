{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0123 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; M0 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; sym ; trans ; ε ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 as MV00635
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00641 as MV00641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00785 as MV00785
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X12 • K0123 ≈ M0 • K0123 • M0 • K0123 • M0
proved = GL.•-cancelʳ {g = X12 • K0123} {g' = M0 • K0123 • M0 • K0123 • M0} {h = p (ε)}
  (trans (sym (move-product MV00785.proved (MV00641.proved))) (trans (cong refl Base.proved) (move-product MV00635.proved (move-product MV00641.proved (move-product MV00635.proved (move-product MV00641.proved (MV00635.proved)))))))
