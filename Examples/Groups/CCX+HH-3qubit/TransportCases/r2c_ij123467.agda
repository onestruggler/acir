{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij123467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3467 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01223 as MV01223
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01224 as MV01224
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K3467 ≈ K3467 • X12
proved = GL.•-cancelʳ {g = X12 • K3467} {g' = K3467 • X12} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01223.proved (MV01224.proved))) (trans (cong refl Base.proved) (move-product MV01224.proved (MV01223.proved))))
