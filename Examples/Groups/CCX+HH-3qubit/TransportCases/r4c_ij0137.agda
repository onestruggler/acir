{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; X17 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00648 as MV00648
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02584 as MV02584
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02970 as MV02970
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X37 • K0137 ≈ K0137 • X17
proved = GL.•-cancelʳ {g = X37 • K0137} {g' = K0137 • X17} {h = p (s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02970.proved (MV00648.proved))) (trans (cong refl Base.proved) (move-product MV00648.proved (MV02584.proved))))
