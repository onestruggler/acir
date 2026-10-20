{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij341256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01526 as MV01526
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01527 as MV01527
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K1256 ≈ K1256 • X34
proved = GL.•-cancelʳ {g = X34 • K1256} {g' = K1256 • X34} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01526.proved (MV01527.proved))) (trans (cong refl Base.proved) (move-product MV01527.proved (MV01526.proved))))
