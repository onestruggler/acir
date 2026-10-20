{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03461257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0346 ; K1257 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00666 as MV00666
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02406 as MV02406
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0346 • K1257 ≈ K1257 • K0346
proved = GL.•-cancelʳ {g = K0346 • K1257} {g' = K1257 • K0346} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00666.proved (MV02406.proved))) (trans (cong refl Base.proved) (move-product MV02406.proved (MV00666.proved))))
