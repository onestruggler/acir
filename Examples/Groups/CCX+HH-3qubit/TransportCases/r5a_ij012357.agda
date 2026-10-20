{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0125 ; K1357 ; K2357 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01742 as MV01742
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03041 as MV03041
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03042 as MV03042
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03043 as MV03043
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0123 • K1357 ≈ K2357 • K0125
proved = GL.•-cancelʳ {g = K0123 • K1357} {g' = K2357 • K0125} {h = p (s4 • s6 • s5)}
  (trans (sym (move-product MV01742.proved (MV03041.proved))) (trans (cong refl Base.proved) (move-product MV03042.proved (MV03043.proved))))
