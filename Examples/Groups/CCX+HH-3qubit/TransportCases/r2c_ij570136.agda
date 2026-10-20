{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij570136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01749 as MV01749
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01750 as MV01750
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X57 • K0136 ≈ K0136 • X57
proved = GL.•-cancelʳ {g = X57 • K0136} {g' = K0136 • X57} {h = p (s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01749.proved (MV01750.proved))) (trans (cong refl Base.proved) (move-product MV01750.proved (MV01749.proved))))
