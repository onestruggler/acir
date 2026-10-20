{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01096 as MV01096
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01097 as MV01097
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K1256 ≈ K1256 • X04
proved = GL.•-cancelʳ {g = X04 • K1256} {g' = K1256 • X04} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01096.proved (MV01097.proved))) (trans (cong refl Base.proved) (move-product MV01097.proved (MV01096.proved))))
