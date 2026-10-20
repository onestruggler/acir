{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01785 as MV01785
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01786 as MV01786
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0235 ≈ K0235 • X67
proved = GL.•-cancelʳ {g = X67 • K0235} {g' = K0235 • X67} {h = p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01785.proved (MV01786.proved))) (trans (cong refl Base.proved) (move-product MV01786.proved (MV01785.proved))))
