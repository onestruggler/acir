{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01602 as MV01602
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01603 as MV01603
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0146 ≈ K0146 • X37
proved = GL.•-cancelʳ {g = X37 • K0146} {g' = K0146 • X37} {h = p (s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01602.proved (MV01603.proved))) (trans (cong refl Base.proved) (move-product MV01603.proved (MV01602.proved))))
