{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij271456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01505 as MV01505
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01506 as MV01506
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K1456 ≈ K1456 • X27
proved = GL.•-cancelʳ {g = X27 • K1456} {g' = K1456 • X27} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01505.proved (MV01506.proved))) (trans (cong refl Base.proved) (move-product MV01506.proved (MV01505.proved))))
