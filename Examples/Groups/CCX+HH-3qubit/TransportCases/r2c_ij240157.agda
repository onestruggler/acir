{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0157 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01398 as MV01398
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01399 as MV01399
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0157 ≈ K0157 • X24
proved = GL.•-cancelʳ {g = X24 • K0157} {g' = K0157 • X24} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01398.proved (MV01399.proved))) (trans (cong refl Base.proved) (move-product MV01399.proved (MV01398.proved))))
