{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; X16 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00643 as MV00643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02564 as MV02564
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02965 as MV02965
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X26 • K0126 ≈ K0126 • X16
proved = GL.•-cancelʳ {g = X26 • K0126} {g' = K0126 • X16} {h = p (s5 • s4 • s3)}
  (trans (sym (move-product MV02965.proved (MV00643.proved))) (trans (cong refl Base.proved) (move-product MV00643.proved (MV02564.proved))))
