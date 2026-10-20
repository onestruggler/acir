{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij563 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01004 as MV01004
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01005 as MV01005
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X56 • M3 ≈ M3 • X56
proved = GL.•-cancelʳ {g = X56 • M3} {g' = M3 • X56} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01004.proved (MV01005.proved))) (trans (cong refl Base.proved) (move-product MV01005.proved (MV01004.proved))))
