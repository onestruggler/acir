{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij031256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01072 as MV01072
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K1256 ≈ K1256 • X03
proved = GL.•-cancelʳ {g = X03 • K1256} {g' = K1256 • X03} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV01072.proved (MV00682.proved))) (trans (cong refl Base.proved) (move-product MV00682.proved (MV01072.proved))))
