{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0236 ; X26 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00657 as MV00657
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02620 as MV02620
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02979 as MV02979
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X36 • K0236 ≈ K0236 • X26
proved = GL.•-cancelʳ {g = X36 • K0236} {g' = K0236 • X26} {h = p (s1 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02979.proved (MV00657.proved))) (trans (cong refl Base.proved) (move-product MV00657.proved (MV02620.proved))))
