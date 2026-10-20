{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij024567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; K0246 ; K2567 ; K4567 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01788 as MV01788
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03086 as MV03086
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03087 as MV03087
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03088 as MV03088
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0245 • K2567 ≈ K4567 • K0246
proved = GL.•-cancelʳ {g = K0245 • K2567} {g' = K4567 • K0246} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01788.proved (MV03086.proved))) (trans (cong refl Base.proved) (move-product MV03087.proved (MV03088.proved))))
