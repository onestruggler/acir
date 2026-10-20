{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3567 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00708 as MV00708
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02824 as MV02824
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03030 as MV03030
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K3567 ≈ K3567 • X57
proved = GL.•-cancelʳ {g = X67 • K3567} {g' = K3567 • X57} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03030.proved (MV00708.proved))) (trans (cong refl Base.proved) (move-product MV00708.proved (MV02824.proved))))
