{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1456 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01075 as MV01075
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01076 as MV01076
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1456 ≈ K1456 • X03
proved = GL.•-cancelʳ {g = X03 • K1456} {g' = K1456 • X03} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01075.proved (MV01076.proved))) (trans (cong refl Base.proved) (move-product MV01076.proved (MV01075.proved))))
