{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij035 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X03 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00731 as MV00731
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00732 as MV00732
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X03 • M5 ≈ M5 • X03
proved = GL.•-cancelʳ {g = X03 • M5} {g' = M5 • X03} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2)}
  (trans (sym (move-product MV00731.proved (MV00732.proved))) (trans (cong refl Base.proved) (move-product MV00732.proved (MV00731.proved))))
