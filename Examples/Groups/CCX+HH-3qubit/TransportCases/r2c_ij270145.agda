{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01485 as MV01485
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01486 as MV01486
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0145 ≈ K0145 • X27
proved = GL.•-cancelʳ {g = X27 • K0145} {g' = K0145 • X27} {h = p (s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01485.proved (MV01486.proved))) (trans (cong refl Base.proved) (move-product MV01486.proved (MV01485.proved))))
