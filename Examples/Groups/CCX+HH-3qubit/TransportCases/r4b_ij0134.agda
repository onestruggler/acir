{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_ij0134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; M0 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00645 as MV00645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01803 as MV01803
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02837 as MV02837
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as Base

proved : X13 • K0134 ≈ M0 • K0134 • M0 • K0134 • M0
proved = GL.•-cancelʳ {g = X13 • K0134} {g' = M0 • K0134 • M0 • K0134 • M0} {h = p (s2 • s3)}
  (trans (sym (move-product MV02837.proved (MV00645.proved))) (trans (cong refl Base.proved) (move-product MV01803.proved (move-product MV00645.proved (move-product MV01803.proved (move-product MV00645.proved (MV01803.proved)))))))
