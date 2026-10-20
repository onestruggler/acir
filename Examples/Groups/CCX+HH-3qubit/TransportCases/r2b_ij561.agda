{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij561 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01000 as MV01000
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01001 as MV01001
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X56 • M1 ≈ M1 • X56
proved = GL.•-cancelʳ {g = X56 • M1} {g' = M1 • X56} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01000.proved (MV01001.proved))) (trans (cong refl Base.proved) (move-product MV01001.proved (MV01000.proved))))
