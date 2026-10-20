{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij370456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01612 as MV01612
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01613 as MV01613
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X37 • K0456 ≈ K0456 • X37
proved = GL.•-cancelʳ {g = X37 • K0456} {g' = K0456 • X37} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01612.proved (MV01613.proved))) (trans (cong refl Base.proved) (move-product MV01613.proved (MV01612.proved))))
