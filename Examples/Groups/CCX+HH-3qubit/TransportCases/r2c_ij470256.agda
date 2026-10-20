{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01697 as MV01697
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01698 as MV01698
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0256 ≈ K0256 • X47
proved = GL.•-cancelʳ {g = X47 • K0256} {g' = K0256 • X47} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01697.proved (MV01698.proved))) (trans (cong refl Base.proved) (move-product MV01698.proved (MV01697.proved))))
