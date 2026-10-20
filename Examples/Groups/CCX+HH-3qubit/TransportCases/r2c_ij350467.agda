{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01552 as MV01552
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01553 as MV01553
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0467 ≈ K0467 • X35
proved = GL.•-cancelʳ {g = X35 • K0467} {g' = K0467 • X35} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
  (trans (sym (move-product MV01552.proved (MV01553.proved))) (trans (cong refl Base.proved) (move-product MV01553.proved (MV01552.proved))))
