{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij240567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; X24 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01408 as MV01408
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01409 as MV01409
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X24 • K0567 ≈ K0567 • X24
proved = GL.•-cancelʳ {g = X24 • K0567} {g' = K0567 • X24} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01408.proved (MV01409.proved))) (trans (cong refl Base.proved) (move-product MV01409.proved (MV01408.proved))))
