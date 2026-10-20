{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij123456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01219 as MV01219
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01220 as MV01220
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K3456 ≈ K3456 • X12
proved = GL.•-cancelʳ {g = X12 • K3456} {g' = K3456 • X12} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01219.proved (MV01220.proved))) (trans (cong refl Base.proved) (move-product MV01220.proved (MV01219.proved))))
