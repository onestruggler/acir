{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij561347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01737 as MV01737
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01738 as MV01738
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K1347 ≈ K1347 • X56
proved = GL.•-cancelʳ {g = X56 • K1347} {g' = K1347 • X56} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01737.proved (MV01738.proved))) (trans (cong refl Base.proved) (move-product MV01738.proved (MV01737.proved))))
