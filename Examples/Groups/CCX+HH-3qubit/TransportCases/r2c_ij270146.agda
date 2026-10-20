{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij270146 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; X27 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01487 as MV01487
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01488 as MV01488
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X27 • K0146 ≈ K0146 • X27
proved = GL.•-cancelʳ {g = X27 • K0146} {g' = K0146 • X27} {h = p (s3 • s2 • s5 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01487.proved (MV01488.proved))) (trans (cong refl Base.proved) (move-product MV01488.proved (MV01487.proved))))
