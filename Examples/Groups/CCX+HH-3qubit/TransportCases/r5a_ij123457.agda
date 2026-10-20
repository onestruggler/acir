{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij123457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; K1235 ; K2457 ; K3457 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01762 as MV01762
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03095 as MV03095
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03096 as MV03096
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03097 as MV03097
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K1234 • K2457 ≈ K3457 • K1235
proved = GL.•-cancelʳ {g = K1234 • K2457} {g' = K3457 • K1235} {h = p (s0 • s1 • s2 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01762.proved (MV03095.proved))) (trans (cong refl Base.proved) (move-product MV03096.proved (MV03097.proved))))
