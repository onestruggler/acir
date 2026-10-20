{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01536 as MV01536
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01537 as MV01537
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0126 ≈ K0126 • X35
proved = GL.•-cancelʳ {g = X35 • K0126} {g' = K0126 • X35} {h = p (s5 • s4 • s3 • s5)}
  (trans (sym (move-product MV01536.proved (MV01537.proved))) (trans (cong refl Base.proved) (move-product MV01537.proved (MV01536.proved))))
