{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0367 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01641 as MV01641
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01642 as MV01642
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0367 ≈ K0367 • X45
proved = GL.•-cancelʳ {g = X45 • K0367} {g' = K0367 • X45} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01641.proved (MV01642.proved))) (trans (cong refl Base.proved) (move-product MV01642.proved (MV01641.proved))))
