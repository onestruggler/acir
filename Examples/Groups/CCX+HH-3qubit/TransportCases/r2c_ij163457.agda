{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij163457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; X16 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01337 as MV01337
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01338 as MV01338
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X16 • K3457 ≈ K3457 • X16
proved = GL.•-cancelʳ {g = X16 • K3457} {g' = K3457 • X16} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01337.proved (MV01338.proved))) (trans (cong refl Base.proved) (move-product MV01338.proved (MV01337.proved))))
