{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij560347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01729 as MV01729
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01730 as MV01730
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X56 • K0347 ≈ K0347 • X56
proved = GL.•-cancelʳ {g = X56 • K0347} {g' = K0347 • X56} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01729.proved (MV01730.proved))) (trans (cong refl Base.proved) (move-product MV01730.proved (MV01729.proved))))
