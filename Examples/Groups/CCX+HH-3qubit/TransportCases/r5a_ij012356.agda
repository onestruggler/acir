{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r5a_ij012356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0125 ; K1356 ; K2356 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01712 as MV01712
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03038 as MV03038
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03039 as MV03039
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03040 as MV03040
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 as Base

proved : K0123 • K1356 ≈ K2356 • K0125
proved = GL.•-cancelʳ {g = K0123 • K1356} {g' = K2356 • K0125} {h = p (s4 • s5)}
  (trans (sym (move-product MV01712.proved (MV03038.proved))) (trans (cong refl Base.proved) (move-product MV03039.proved (MV03040.proved))))
