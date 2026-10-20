{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670134 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01777 as MV01777
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01778 as MV01778
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0134 ≈ K0134 • X67
proved = GL.•-cancelʳ {g = X67 • K0134} {g' = K0134 • X67} {h = p (s2 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01777.proved (MV01778.proved))) (trans (cong refl Base.proved) (move-product MV01778.proved (MV01777.proved))))
