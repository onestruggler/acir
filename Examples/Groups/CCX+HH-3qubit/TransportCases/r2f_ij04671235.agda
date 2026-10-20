{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij04671235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; K1235 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00673 as MV00673
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02413 as MV02413
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0467 • K1235 ≈ K1235 • K0467
proved = GL.•-cancelʳ {g = K0467 • K1235} {g' = K1235 • K0467} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00673.proved (MV02413.proved))) (trans (cong refl Base.proved) (move-product MV02413.proved (MV00673.proved))))
