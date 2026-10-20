{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1267 ; X27 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00684 as MV00684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02728 as MV02728
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03006 as MV03006
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K1267 ≈ K1267 • X27
proved = GL.•-cancelʳ {g = X67 • K1267} {g' = K1267 • X27} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03006.proved (MV00684.proved))) (trans (cong refl Base.proved) (move-product MV00684.proved (MV02728.proved))))
