{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij12670345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; K1267 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00684 as MV00684
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02424 as MV02424
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K1267 • K0345 ≈ K0345 • K1267
proved = GL.•-cancelʳ {g = K1267 • K0345} {g' = K0345 • K1267} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00684.proved (MV02424.proved))) (trans (cong refl Base.proved) (move-product MV02424.proved (MV00684.proved))))
