{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01491 as MV01491
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01492 as MV01492
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0345 ≈ K0345 • X27
proved = GL.•-cancelʳ {g = X27 • K0345} {g' = K0345 • X27} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01491.proved (MV01492.proved))) (trans (cong refl Base.proved) (move-product MV01492.proved (MV01491.proved))))
