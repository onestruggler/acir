{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij134567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; X13 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01251 as MV01251
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01252 as MV01252
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X13 • K4567 ≈ K4567 • X13
proved = GL.•-cancelʳ {g = X13 • K4567} {g' = K4567 • X13} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01251.proved (MV01252.proved))) (trans (cong refl Base.proved) (move-product MV01252.proved (MV01251.proved))))
