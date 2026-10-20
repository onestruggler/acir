{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01781 as MV01781
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01782 as MV01782
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0145 ≈ K0145 • X67
proved = GL.•-cancelʳ {g = X67 • K0145} {g' = K0145 • X67} {h = p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01781.proved (MV01782.proved))) (trans (cong refl Base.proved) (move-product MV01782.proved (MV01781.proved))))
