{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01008 as MV01008
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01009 as MV01009
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X56 • M7 ≈ M7 • X56
proved = GL.•-cancelʳ {g = X56 • M7} {g' = M7 • X56} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01008.proved (MV01009.proved))) (trans (cong refl Base.proved) (move-product MV01009.proved (MV01008.proved))))
