{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01453 as MV01453
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01454 as MV01454
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0137 ≈ K0137 • X26
proved = GL.•-cancelʳ {g = X26 • K0137} {g' = K0137 • X26} {h = p (s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01453.proved (MV01454.proved))) (trans (cong refl Base.proved) (move-product MV01454.proved (MV01453.proved))))
