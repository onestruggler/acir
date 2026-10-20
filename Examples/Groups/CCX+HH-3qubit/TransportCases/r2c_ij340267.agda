{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij340267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; X34 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01522 as MV01522
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01523 as MV01523
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X34 • K0267 ≈ K0267 • X34
proved = GL.•-cancelʳ {g = X34 • K0267} {g' = K0267 • X34} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01522.proved (MV01523.proved))) (trans (cong refl Base.proved) (move-product MV01523.proved (MV01522.proved))))
