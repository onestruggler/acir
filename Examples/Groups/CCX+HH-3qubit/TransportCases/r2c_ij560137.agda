{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01719 as MV01719
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01720 as MV01720
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0137 ≈ K0137 • X56
proved = GL.•-cancelʳ {g = X56 • K0137} {g' = K0137 • X56} {h = p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01719.proved (MV01720.proved))) (trans (cong refl Base.proved) (move-product MV01720.proved (MV01719.proved))))
