{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij52 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; M5 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01865 as MV01865
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01866 as MV01866
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M5 • M2 ≈ M2 • M5
proved = GL.•-cancelʳ {g = M5 • M2} {g' = M2 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s3)}
  (trans (sym (move-product MV01865.proved (MV01866.proved))) (trans (cong refl Base.proved) (move-product MV01866.proved (MV01865.proved))))
