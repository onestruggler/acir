{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij150236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01281 as MV01281
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01282 as MV01282
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K0236 ≈ K0236 • X15
proved = GL.•-cancelʳ {g = X15 • K0236} {g' = K0236 • X15} {h = p (s1 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01281.proved (MV01282.proved))) (trans (cong refl Base.proved) (move-product MV01282.proved (MV01281.proved))))
