{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij451237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01645 as MV01645
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01646 as MV01646
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K1237 ≈ K1237 • X45
proved = GL.•-cancelʳ {g = X45 • K1237} {g' = K1237 • X45} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01645.proved (MV01646.proved))) (trans (cong refl Base.proved) (move-product MV01646.proved (MV01645.proved))))
