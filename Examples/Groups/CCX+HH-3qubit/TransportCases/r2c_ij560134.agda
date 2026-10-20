{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01717 as MV01717
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01718 as MV01718
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0134 ≈ K0134 • X56
proved = GL.•-cancelʳ {g = X56 • K0134} {g' = K0134 • X56} {h = p (s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01717.proved (MV01718.proved))) (trans (cong refl Base.proved) (move-product MV01718.proved (MV01717.proved))))
