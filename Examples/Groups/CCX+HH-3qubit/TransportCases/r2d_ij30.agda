{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij30 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01835 as MV01835
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01836 as MV01836
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M3 • M0 ≈ M0 • M3
proved = GL.•-cancelʳ {g = M3 • M0} {g' = M0 • M3} {h = p (s2 • s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01835.proved (MV01836.proved))) (trans (cong refl Base.proved) (move-product MV01836.proved (MV01835.proved))))
