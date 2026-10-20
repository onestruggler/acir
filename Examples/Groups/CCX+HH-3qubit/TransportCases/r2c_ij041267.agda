{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01100 as MV01100
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01101 as MV01101
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K1267 ≈ K1267 • X04
proved = GL.•-cancelʳ {g = X04 • K1267} {g' = K1267 • X04} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01100.proved (MV01101.proved))) (trans (cong refl Base.proved) (move-product MV01101.proved (MV01100.proved))))
