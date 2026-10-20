{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij013456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K0135 ; K1456 ; K3456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01718 as MV01718
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03059 as MV03059
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03060 as MV03060
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03061 as MV03061
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0134 • K1456 ≈ K3456 • K0135
proved = GL.•-cancelʳ {g = K0134 • K1456} {g' = K3456 • K0135} {h = p (s2 • s3 • s4 • s5)}
  (trans (sym (move-product MV01718.proved (MV03059.proved))) (trans (cong refl Base.proved) (move-product MV03060.proved (MV03061.proved))))
