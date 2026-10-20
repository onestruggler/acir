{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01625 as MV01625
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01626 as MV01626
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0126 ≈ K0126 • X45
proved = GL.•-cancelʳ {g = X45 • K0126} {g' = K0126 • X45} {h = p (s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01625.proved (MV01626.proved))) (trans (cong refl Base.proved) (move-product MV01626.proved (MV01625.proved))))
