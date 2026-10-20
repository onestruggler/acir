{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01550 as MV01550
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01551 as MV01551
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0267 ≈ K0267 • X35
proved = GL.•-cancelʳ {g = X35 • K0267} {g' = K0267 • X35} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01550.proved (MV01551.proved))) (trans (cong refl Base.proved) (move-product MV01551.proved (MV01550.proved))))
