{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01514 as MV01514
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01515 as MV01515
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0157 ≈ K0157 • X34
proved = GL.•-cancelʳ {g = X34 • K0157} {g' = K0157 • X34} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01514.proved (MV01515.proved))) (trans (cong refl Base.proved) (move-product MV01515.proved (MV01514.proved))))
