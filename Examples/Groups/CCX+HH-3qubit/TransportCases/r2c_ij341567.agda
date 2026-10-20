{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij341567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01532 as MV01532
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01533 as MV01533
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K1567 ≈ K1567 • X34
proved = GL.•-cancelʳ {g = X34 • K1567} {g' = K1567 • X34} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01532.proved (MV01533.proved))) (trans (cong refl Base.proved) (move-product MV01533.proved (MV01532.proved))))
