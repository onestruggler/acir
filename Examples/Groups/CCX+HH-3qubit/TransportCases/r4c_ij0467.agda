{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; X47 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02684 as MV02684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02995 as MV02995
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K0467 ≈ K0467 • X47
proved = GL.•-cancelʳ {g = X67 • K0467} {g' = K0467 • X47} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02995.proved (MV00673.proved))) (trans (cong refl Base.proved) (move-product MV00673.proved (MV02684.proved))))
