{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560124 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01713 as MV01713
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01714 as MV01714
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0124 ≈ K0124 • X56
proved = GL.•-cancelʳ {g = X56 • K0124} {g' = K0124 • X56} {h = p (s3 • s4 • s5)}
  (trans (sym (move-product MV01713.proved (MV01714.proved))) (trans (cong refl Base.proved) (move-product MV01714.proved (MV01713.proved))))
