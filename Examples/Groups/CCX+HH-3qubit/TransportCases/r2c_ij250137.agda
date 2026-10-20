{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01423 as MV01423
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01424 as MV01424
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0137 ≈ K0137 • X25
proved = GL.•-cancelʳ {g = X25 • K0137} {g' = K0137 • X25} {h = p (s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01423.proved (MV01424.proved))) (trans (cong refl Base.proved) (move-product MV01424.proved (MV01423.proved))))
