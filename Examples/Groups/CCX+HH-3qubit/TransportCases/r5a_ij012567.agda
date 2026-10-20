{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; K0126 ; K1567 ; K2567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01776 as MV01776
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03056 as MV03056
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03057 as MV03057
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03058 as MV03058
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0125 • K1567 ≈ K2567 • K0126
proved = GL.•-cancelʳ {g = K0125 • K1567} {g' = K2567 • K0126} {h = p (s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01776.proved (MV03056.proved))) (trans (cong refl Base.proved) (move-product MV03057.proved (MV03058.proved))))
