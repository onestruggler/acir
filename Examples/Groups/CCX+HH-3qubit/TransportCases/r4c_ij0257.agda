{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0257 ; X27 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00663 as MV00663
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02644 as MV02644
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02985 as MV02985
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X57 • K0257 ≈ K0257 • X27
proved = GL.•-cancelʳ {g = X57 • K0257} {g' = K0257 • X27} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02985.proved (MV00663.proved))) (trans (cong refl Base.proved) (move-product MV00663.proved (MV02644.proved))))
