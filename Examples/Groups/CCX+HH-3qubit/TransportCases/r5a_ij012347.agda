{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K1347 ; K2347 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01682 as MV01682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03035 as MV03035
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03036 as MV03036
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03037 as MV03037
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0123 • K1347 ≈ K2347 • K0124
proved = GL.•-cancelʳ {g = K0123 • K1347} {g' = K2347 • K0124} {h = p (s6 • s5)}
  (trans (sym (move-product MV01682.proved (MV03035.proved))) (trans (cong refl Base.proved) (move-product MV03036.proved (MV03037.proved))))
