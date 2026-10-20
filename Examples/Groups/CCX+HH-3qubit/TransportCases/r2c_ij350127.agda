{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350127 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0127 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01538 as MV01538
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01539 as MV01539
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0127 ≈ K0127 • X35
proved = GL.•-cancelʳ {g = X35 • K0127} {g' = K0127 • X35} {h = p (s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01538.proved (MV01539.proved))) (trans (cong refl Base.proved) (move-product MV01539.proved (MV01538.proved))))
