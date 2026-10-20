{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0567 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00674 as MV00674
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02688 as MV02688
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02996 as MV02996
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K0567 ≈ K0567 • X57
proved = GL.•-cancelʳ {g = X67 • K0567} {g' = K0567 • X57} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02996.proved (MV00674.proved))) (trans (cong refl Base.proved) (move-product MV00674.proved (MV02688.proved))))
