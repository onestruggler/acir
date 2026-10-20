{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij350246 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0246 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01546 as MV01546
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01547 as MV01547
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X35 • K0246 ≈ K0246 • X35
proved = GL.•-cancelʳ {g = X35 • K0246} {g' = K0246 • X35} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01546.proved (MV01547.proved))) (trans (cong refl Base.proved) (move-product MV01547.proved (MV01546.proved))))
