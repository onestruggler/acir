{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01596 as MV01596
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01597 as MV01597
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0125 ≈ K0125 • X37
proved = GL.•-cancelʳ {g = X37 • K0125} {g' = K0125 • X37} {h = p (s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01596.proved (MV01597.proved))) (trans (cong refl Base.proved) (move-product MV01597.proved (MV01596.proved))))
