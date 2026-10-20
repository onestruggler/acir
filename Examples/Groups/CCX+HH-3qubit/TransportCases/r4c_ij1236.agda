{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1236 ; X26 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00677 as MV00677
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02700 as MV02700
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02999 as MV02999
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X36 • K1236 ≈ K1236 • X26
proved = GL.•-cancelʳ {g = X36 • K1236} {g' = K1236 • X26} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02999.proved (MV00677.proved))) (trans (cong refl Base.proved) (move-product MV00677.proved (MV02700.proved))))
