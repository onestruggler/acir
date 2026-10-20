{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij124567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; K1246 ; K2567 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01796 as MV01796
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03104 as MV03104
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03105 as MV03105
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03106 as MV03106
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K1245 • K2567 ≈ K4567 • K1246
proved = GL.•-cancelʳ {g = K1245 • K2567} {g' = K4567 • K1246} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01796.proved (MV03104.proved))) (trans (cong refl Base.proved) (move-product MV03105.proved (MV03106.proved))))
