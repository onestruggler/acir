{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij260357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0357 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01465 as MV01465
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01466 as MV01466
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X26 • K0357 ≈ K0357 • X26
proved = GL.•-cancelʳ {g = X26 • K0357} {g' = K0357 • X26} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01465.proved (MV01466.proved))) (trans (cong refl Base.proved) (move-product MV01466.proved (MV01465.proved))))
