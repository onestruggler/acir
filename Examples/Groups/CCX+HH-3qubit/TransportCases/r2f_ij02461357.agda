{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02461357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; K1357 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00660 as MV00660
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02400 as MV02400
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0246 • K1357 ≈ K1357 • K0246
proved = GL.•-cancelʳ {g = K0246 • K1357} {g' = K1357 • K0246} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV00660.proved (MV02400.proved))) (trans (cong refl Base.proved) (move-product MV02400.proved (MV00660.proved))))
