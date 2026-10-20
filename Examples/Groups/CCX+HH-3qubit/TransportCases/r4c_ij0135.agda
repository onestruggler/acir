{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0135 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; X15 ; X35 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02576 as MV02576
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02968 as MV02968
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X35 • K0135 ≈ K0135 • X15
proved = GL.•-cancelʳ {g = X35 • K0135} {g' = K0135 • X15} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV02968.proved (MV00646.proved))) (trans (cong refl Base.proved) (move-product MV00646.proved (MV02576.proved))))
