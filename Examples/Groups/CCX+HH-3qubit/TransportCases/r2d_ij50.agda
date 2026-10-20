{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij50 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01861 as MV01861
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01862 as MV01862
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M5 • M0 ≈ M0 • M5
proved = GL.•-cancelʳ {g = M5 • M0} {g' = M0 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)}
  (trans (sym (move-product MV01861.proved (MV01862.proved))) (trans (cong refl Base.proved) (move-product MV01862.proved (MV01861.proved))))
