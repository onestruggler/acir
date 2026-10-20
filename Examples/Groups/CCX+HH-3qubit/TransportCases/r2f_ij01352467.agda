{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij01352467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K2467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00646 as MV00646
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02386 as MV02386
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0135 • K2467 ≈ K2467 • K0135
proved = GL.•-cancelʳ {g = K0135 • K2467} {g' = K2467 • K0135} {h = p (s2 • s4 • s3)}
  (trans (sym (move-product MV00646.proved (MV02386.proved))) (trans (cong refl Base.proved) (move-product MV02386.proved (MV00646.proved))))
