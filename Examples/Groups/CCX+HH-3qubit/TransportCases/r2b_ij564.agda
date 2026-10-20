{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij564 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01006 as MV01006
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01007 as MV01007
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X56 • M4 ≈ M4 • X56
proved = GL.•-cancelʳ {g = X56 • M4} {g' = M4 • X56} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01006.proved (MV01007.proved))) (trans (cong refl Base.proved) (move-product MV01007.proved (MV01006.proved))))
