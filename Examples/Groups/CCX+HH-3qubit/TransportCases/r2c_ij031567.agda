{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01081 as MV01081
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01082 as MV01082
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1567 ≈ K1567 • X03
proved = GL.•-cancelʳ {g = X03 • K1567} {g' = K1567 • X03} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01081.proved (MV01082.proved))) (trans (cong refl Base.proved) (move-product MV01082.proved (MV01081.proved))))
