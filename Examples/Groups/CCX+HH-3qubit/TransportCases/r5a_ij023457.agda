{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij023457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; K2457 ; K3457 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01754 as MV01754
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03077 as MV03077
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03078 as MV03078
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03079 as MV03079
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0234 • K2457 ≈ K3457 • K0235
proved = GL.•-cancelʳ {g = K0234 • K2457} {g' = K3457 • K0235} {h = p (s1 • s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01754.proved (MV03077.proved))) (trans (cong refl Base.proved) (move-product MV03078.proved (MV03079.proved))))
