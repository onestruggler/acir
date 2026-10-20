{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij250467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; X25 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01437 as MV01437
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01438 as MV01438
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X25 • K0467 ≈ K0467 • X25
proved = GL.•-cancelʳ {g = X25 • K0467} {g' = K0467 • X25} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01437.proved (MV01438.proved))) (trans (cong refl Base.proved) (move-product MV01438.proved (MV01437.proved))))
