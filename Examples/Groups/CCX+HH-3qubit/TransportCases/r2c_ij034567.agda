{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij034567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01091 as MV01091
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01092 as MV01092
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K4567 ≈ K4567 • X03
proved = GL.•-cancelʳ {g = X03 • K4567} {g' = K4567 • X03} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01091.proved (MV01092.proved))) (trans (cong refl Base.proved) (move-product MV01092.proved (MV01091.proved))))
