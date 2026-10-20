{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij470136 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01689 as MV01689
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01690 as MV01690
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X47 • K0136 ≈ K0136 • X47
proved = GL.•-cancelʳ {g = X47 • K0136} {g' = K0136 • X47} {h = p (s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01689.proved (MV01690.proved))) (trans (cong refl Base.proved) (move-product MV01690.proved (MV01689.proved))))
