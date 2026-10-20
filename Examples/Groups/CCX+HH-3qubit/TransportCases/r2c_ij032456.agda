{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij032456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2456 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01083 as MV01083
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01084 as MV01084
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X03 • K2456 ≈ K2456 • X03
proved = GL.•-cancelʳ {g = X03 • K2456} {g' = K2456 • X03} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01083.proved (MV01084.proved))) (trans (cong refl Base.proved) (move-product MV01084.proved (MV01083.proved))))
