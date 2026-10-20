{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij231456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01383 as MV01383
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01384 as MV01384
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K1456 ≈ K1456 • X23
proved = GL.•-cancelʳ {g = X23 • K1456} {g' = K1456 • X23} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01383.proved (MV01384.proved))) (trans (cong refl Base.proved) (move-product MV01384.proved (MV01383.proved))))
