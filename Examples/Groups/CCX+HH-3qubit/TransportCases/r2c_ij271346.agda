{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij271346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01501 as MV01501
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01502 as MV01502
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K1346 ≈ K1346 • X27
proved = GL.•-cancelʳ {g = X27 • K1346} {g' = K1346 • X27} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01501.proved (MV01502.proved))) (trans (cong refl Base.proved) (move-product MV01502.proved (MV01501.proved))))
