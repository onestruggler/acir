{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij130246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01230 as MV01230
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K0246 ≈ K0246 • X13
proved = GL.•-cancelʳ {g = X13 • K0246} {g' = K0246 • X13} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01230.proved (MV00660.proved))) (trans (cong refl Base.proved) (move-product MV00660.proved (MV01230.proved))))
