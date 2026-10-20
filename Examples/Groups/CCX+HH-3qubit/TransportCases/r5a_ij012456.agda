{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; K0125 ; K1456 ; K2456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01714 as MV01714
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03047 as MV03047
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03048 as MV03048
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03049 as MV03049
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0124 • K1456 ≈ K2456 • K0125
proved = GL.•-cancelʳ {g = K0124 • K1456} {g' = K2456 • K0125} {h = p (s3 • s4 • s5)}
  (trans (sym (move-product MV01714.proved (MV03047.proved))) (trans (cong refl Base.proved) (move-product MV03048.proved (MV03049.proved))))
