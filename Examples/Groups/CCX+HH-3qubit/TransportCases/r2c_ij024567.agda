{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij024567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; X02 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01067 as MV01067
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01068 as MV01068
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X02 • K4567 ≈ K4567 • X02
proved = GL.•-cancelʳ {g = X02 • K4567} {g' = K4567 • X02} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01067.proved (MV01068.proved))) (trans (cong refl Base.proved) (move-product MV01068.proved (MV01067.proved))))
