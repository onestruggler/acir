{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01672345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; K2345 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02394 as MV02394
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0167 • K2345 ≈ K2345 • K0167
proved = GL.•-cancelʳ {g = K0167 • K2345} {g' = K2345 • K0167} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00654.proved (MV02394.proved))) (trans (cong refl Base.proved) (move-product MV02394.proved (MV00654.proved))))
