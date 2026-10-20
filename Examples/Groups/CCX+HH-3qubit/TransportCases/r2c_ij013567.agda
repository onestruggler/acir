{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij013567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; X01 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01047 as MV01047
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X01 • K3567 ≈ K3567 • X01
proved = GL.•-cancelʳ {g = X01 • K3567} {g' = K3567 • X01} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV01047.proved (MV00708.proved))) (trans (cong refl Base.proved) (move-product MV00708.proved (MV01047.proved))))
