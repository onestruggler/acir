{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij671245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01795 as MV01795
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01796 as MV01796
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K1245 ≈ K1245 • X67
proved = GL.•-cancelʳ {g = X67 • K1245} {g' = K1245 • X67} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01795.proved (MV01796.proved))) (trans (cong refl Base.proved) (move-product MV01796.proved (MV01795.proved))))
