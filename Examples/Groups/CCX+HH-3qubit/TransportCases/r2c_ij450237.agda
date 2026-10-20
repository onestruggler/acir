{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij450237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01637 as MV01637
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01638 as MV01638
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X45 • K0237 ≈ K0237 • X45
proved = GL.•-cancelʳ {g = X45 • K0237} {g' = K0237 • X45} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01637.proved (MV01638.proved))) (trans (cong refl Base.proved) (move-product MV01638.proved (MV01637.proved))))
