{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00653 as MV00653
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01373 as MV01373
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K0157 ≈ K0157 • X23
proved = GL.•-cancelʳ {g = X23 • K0157} {g' = K0157 • X23} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01373.proved (MV00653.proved))) (trans (cong refl Base.proved) (move-product MV00653.proved (MV01373.proved))))
