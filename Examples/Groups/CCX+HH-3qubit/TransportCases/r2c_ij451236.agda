{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij451236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01643 as MV01643
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01644 as MV01644
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K1236 ≈ K1236 • X45
proved = GL.•-cancelʳ {g = X45 • K1236} {g' = K1236 • X45} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01643.proved (MV01644.proved))) (trans (cong refl Base.proved) (move-product MV01644.proved (MV01643.proved))))
