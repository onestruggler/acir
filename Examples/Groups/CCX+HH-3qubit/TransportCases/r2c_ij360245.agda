{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij360245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01576 as MV01576
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01577 as MV01577
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X36 • K0245 ≈ K0245 • X36
proved = GL.•-cancelʳ {g = X36 • K0245} {g' = K0245 • X36} {h = p (s1 • s3 • s2 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01576.proved (MV01577.proved))) (trans (cong refl Base.proved) (move-product MV01577.proved (MV01576.proved))))
