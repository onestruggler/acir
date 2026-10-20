{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij670245 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0245 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01787 as MV01787
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01788 as MV01788
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X67 • K0245 ≈ K0245 • X67
proved = GL.•-cancelʳ {g = X67 • K0245} {g' = K0245 • X67} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01787.proved (MV01788.proved))) (trans (cong refl Base.proved) (move-product MV01788.proved (MV01787.proved))))
