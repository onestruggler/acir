{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01631 as MV01631
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01632 as MV01632
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0137 ≈ K0137 • X45
proved = GL.•-cancelʳ {g = X45 • K0137} {g' = K0137 • X45} {h = p (s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01631.proved (MV01632.proved))) (trans (cong refl Base.proved) (move-product MV01632.proved (MV01631.proved))))
