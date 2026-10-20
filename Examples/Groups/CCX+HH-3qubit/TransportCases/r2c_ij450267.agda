{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01639 as MV01639
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01640 as MV01640
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0267 ≈ K0267 • X45
proved = GL.•-cancelʳ {g = X45 • K0267} {g' = K0267 • X45} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01639.proved (MV01640.proved))) (trans (cong refl Base.proved) (move-product MV01640.proved (MV01639.proved))))
