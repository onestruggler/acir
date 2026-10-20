{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij231467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1467 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01387 as MV01387
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01388 as MV01388
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K1467 ≈ K1467 • X23
proved = GL.•-cancelʳ {g = X23 • K1467} {g' = K1467 • X23} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01387.proved (MV01388.proved))) (trans (cong refl Base.proved) (move-product MV01388.proved (MV01387.proved))))
