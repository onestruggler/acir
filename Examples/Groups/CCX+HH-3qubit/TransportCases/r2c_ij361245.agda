{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij361245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01584 as MV01584
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01585 as MV01585
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K1245 ≈ K1245 • X36
proved = GL.•-cancelʳ {g = X36 • K1245} {g' = K1245 • X36} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01584.proved (MV01585.proved))) (trans (cong refl Base.proved) (move-product MV01585.proved (MV01584.proved))))
