{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0347 ; X37 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00667 as MV00667
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02660 as MV02660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02989 as MV02989
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X47 • K0347 ≈ K0347 • X37
proved = GL.•-cancelʳ {g = X47 • K0347} {g' = K0347 • X37} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02989.proved (MV00667.proved))) (trans (cong refl Base.proved) (move-product MV00667.proved (MV02660.proved))))
