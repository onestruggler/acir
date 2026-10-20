{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670234 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01783 as MV01783
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01784 as MV01784
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0234 ≈ K0234 • X67
proved = GL.•-cancelʳ {g = X67 • K0234} {g' = K0234 • X67} {h = p (s1 • s2 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01783.proved (MV01784.proved))) (trans (cong refl Base.proved) (move-product MV01784.proved (MV01783.proved))))
