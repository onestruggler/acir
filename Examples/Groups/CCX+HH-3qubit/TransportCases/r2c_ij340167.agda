{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01516 as MV01516
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01517 as MV01517
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0167 ≈ K0167 • X34
proved = GL.•-cancelʳ {g = X34 • K0167} {g' = K0167 • X34} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01516.proved (MV01517.proved))) (trans (cong refl Base.proved) (move-product MV01517.proved (MV01516.proved))))
