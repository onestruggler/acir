{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; X27 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02624 as MV02624
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02980 as MV02980
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X37 • K0237 ≈ K0237 • X27
proved = GL.•-cancelʳ {g = X37 • K0237} {g' = K0237 • X27} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02980.proved (MV00658.proved))) (trans (cong refl Base.proved) (move-product MV00658.proved (MV02624.proved))))
