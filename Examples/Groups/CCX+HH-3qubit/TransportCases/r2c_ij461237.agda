{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij461237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1237 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01673 as MV01673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01674 as MV01674
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X46 • K1237 ≈ K1237 • X46
proved = GL.•-cancelʳ {g = X46 • K1237} {g' = K1237 • X46} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01673.proved (MV01674.proved))) (trans (cong refl Base.proved) (move-product MV01674.proved (MV01673.proved))))
