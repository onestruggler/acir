{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij071345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1345 ; X07 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01191 as MV01191
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01192 as MV01192
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X07 • K1345 ≈ K1345 • X07
proved = GL.•-cancelʳ {g = X07 • K1345} {g' = K1345 • X07} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01191.proved (MV01192.proved))) (trans (cong refl Base.proved) (move-product MV01192.proved (MV01191.proved))))
