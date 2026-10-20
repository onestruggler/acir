{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij124567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; X12 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01227 as MV01227
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01228 as MV01228
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X12 • K4567 ≈ K4567 • X12
proved = GL.•-cancelʳ {g = X12 • K4567} {g' = K4567 • X12} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01227.proved (MV01228.proved))) (trans (cong refl Base.proved) (move-product MV01228.proved (MV01227.proved))))
