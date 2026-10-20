{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1245 ; X25 ; X45 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00679 as MV00679
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02708 as MV02708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03001 as MV03001
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X45 • K1245 ≈ K1245 • X25
proved = GL.•-cancelʳ {g = X45 • K1245} {g' = K1245 • X25} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV03001.proved (MV00679.proved))) (trans (cong refl Base.proved) (move-product MV00679.proved (MV02708.proved))))
