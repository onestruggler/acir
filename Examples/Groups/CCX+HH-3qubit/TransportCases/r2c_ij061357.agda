{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij061357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1357 ; X06 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01165 as MV01165
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01166 as MV01166
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X06 • K1357 ≈ K1357 • X06
proved = GL.•-cancelʳ {g = X06 • K1357} {g' = K1357 • X06} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01165.proved (MV01166.proved))) (trans (cong refl Base.proved) (move-product MV01166.proved (MV01165.proved))))
