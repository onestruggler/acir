{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01570 as MV01570
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01571 as MV01571
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0145 ≈ K0145 • X36
proved = GL.•-cancelʳ {g = X36 • K0145} {g' = K0145 • X36} {h = p (s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01570.proved (MV01571.proved))) (trans (cong refl Base.proved) (move-product MV01571.proved (MV01570.proved))))
