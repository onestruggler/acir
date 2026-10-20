{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00652 as MV00652
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01372 as MV01372
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K0156 ≈ K0156 • X23
proved = GL.•-cancelʳ {g = X23 • K0156} {g' = K0156 • X23} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01372.proved (MV00652.proved))) (trans (cong refl Base.proved) (move-product MV00652.proved (MV01372.proved))))
