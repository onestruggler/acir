{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij261457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1457 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01475 as MV01475
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01476 as MV01476
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K1457 ≈ K1457 • X26
proved = GL.•-cancelʳ {g = X26 • K1457} {g' = K1457 • X26} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01475.proved (MV01476.proved))) (trans (cong refl Base.proved) (move-product MV01476.proved (MV01475.proved))))
