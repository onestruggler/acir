{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij03451267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; K1267 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00665 as MV00665
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02405 as MV02405
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0345 • K1267 ≈ K1267 • K0345
proved = GL.•-cancelʳ {g = K0345 • K1267} {g' = K1267 • K0345} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV00665.proved (MV02405.proved))) (trans (cong refl Base.proved) (move-product MV02405.proved (MV00665.proved))))
