{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij041567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; X04 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01108 as MV01108
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01109 as MV01109
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X04 • K1567 ≈ K1567 • X04
proved = GL.•-cancelʳ {g = X04 • K1567} {g' = K1567 • X04} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01108.proved (MV01109.proved))) (trans (cong refl Base.proved) (move-product MV01109.proved (MV01108.proved))))
