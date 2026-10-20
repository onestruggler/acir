{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij023456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3456 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01059 as MV01059
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01060 as MV01060
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K3456 ≈ K3456 • X02
proved = GL.•-cancelʳ {g = X02 • K3456} {g' = K3456 • X02} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01059.proved (MV01060.proved))) (trans (cong refl Base.proved) (move-product MV01060.proved (MV01059.proved))))
