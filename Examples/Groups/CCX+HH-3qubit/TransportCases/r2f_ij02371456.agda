{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02371456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K1456 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00658 as MV00658
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02398 as MV02398
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0237 • K1456 ≈ K1456 • K0237
proved = GL.•-cancelʳ {g = K0237 • K1456} {g' = K1456 • K0237} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00658.proved (MV02398.proved))) (trans (cong refl Base.proved) (move-product MV02398.proved (MV00658.proved))))
