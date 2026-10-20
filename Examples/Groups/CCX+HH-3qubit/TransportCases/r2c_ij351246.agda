{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij351246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1246 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01554 as MV01554
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01555 as MV01555
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K1246 ≈ K1246 • X35
proved = GL.•-cancelʳ {g = X35 • K1246} {g' = K1246 • X35} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01554.proved (MV01555.proved))) (trans (cong refl Base.proved) (move-product MV01555.proved (MV01554.proved))))
