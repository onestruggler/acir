{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1257 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01159 as MV01159
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01160 as MV01160
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1257 ≈ K1257 • X06
proved = GL.•-cancelʳ {g = X06 • K1257} {g' = K1257 • X06} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01159.proved (MV01160.proved))) (trans (cong refl Base.proved) (move-product MV01160.proved (MV01159.proved))))
