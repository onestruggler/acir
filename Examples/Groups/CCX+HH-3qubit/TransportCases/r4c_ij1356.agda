{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1356 ; X36 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00688 as MV00688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02744 as MV02744
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03010 as MV03010
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K1356 ≈ K1356 • X36
proved = GL.•-cancelʳ {g = X56 • K1356} {g' = K1356 • X36} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03010.proved (MV00688.proved))) (trans (cong refl Base.proved) (move-product MV00688.proved (MV02744.proved))))
