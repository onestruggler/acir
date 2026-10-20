{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij123456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1234 ; K1235 ; K2456 ; K3456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01732 as MV01732
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03092 as MV03092
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03093 as MV03093
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03094 as MV03094
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K1234 • K2456 ≈ K3456 • K1235
proved = GL.•-cancelʳ {g = K1234 • K2456} {g' = K3456 • K1235} {h = p (s0 • s1 • s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01732.proved (MV03092.proved))) (trans (cong refl Base.proved) (move-product MV03093.proved (MV03094.proved))))
