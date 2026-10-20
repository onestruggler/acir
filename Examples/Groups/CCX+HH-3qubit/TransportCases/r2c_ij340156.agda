{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340156 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0156 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01512 as MV01512
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01513 as MV01513
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0156 ≈ K0156 • X34
proved = GL.•-cancelʳ {g = X34 • K0156} {g' = K0156 • X34} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01512.proved (MV01513.proved))) (trans (cong refl Base.proved) (move-product MV01513.proved (MV01512.proved))))
