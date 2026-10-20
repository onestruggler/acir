{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij152467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01305 as MV01305
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01306 as MV01306
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X15 • K2467 ≈ K2467 • X15
proved = GL.•-cancelʳ {g = X15 • K2467} {g' = K2467 • X15} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01305.proved (MV01306.proved))) (trans (cong refl Base.proved) (move-product MV01306.proved (MV01305.proved))))
