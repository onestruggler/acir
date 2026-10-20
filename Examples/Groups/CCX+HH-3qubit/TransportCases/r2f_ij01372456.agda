{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01372456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; K2456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02388 as MV02388
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0137 • K2456 ≈ K2456 • K0137
proved = GL.•-cancelʳ {g = K0137 • K2456} {g' = K2456 • K0137} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00648.proved (MV02388.proved))) (trans (cong refl Base.proved) (move-product MV02388.proved (MV00648.proved))))
