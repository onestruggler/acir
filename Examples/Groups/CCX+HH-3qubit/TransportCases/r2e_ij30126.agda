{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij30126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; M3 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02043 as MV02043
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M3 • K0126 ≈ K0126 • M3
proved = GL.•-cancelʳ {g = M3 • K0126} {g' = K0126 • M3} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV02043.proved (MV00643.proved))) (trans (cong refl Base.proved) (move-product MV00643.proved (MV02043.proved))))
