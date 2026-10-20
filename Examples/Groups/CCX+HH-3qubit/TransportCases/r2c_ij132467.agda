{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij132467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01247 as MV01247
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01248 as MV01248
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K2467 ≈ K2467 • X13
proved = GL.•-cancelʳ {g = X13 • K2467} {g' = K2467 • X13} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01247.proved (MV01248.proved))) (trans (cong refl Base.proved) (move-product MV01248.proved (MV01247.proved))))
