{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij675 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01032 as MV01032
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01033 as MV01033
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X67 • M5 ≈ M5 • X67
proved = GL.•-cancelʳ {g = X67 • M5} {g' = M5 • X67} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01032.proved (MV01033.proved))) (trans (cong refl Base.proved) (move-product MV01033.proved (MV01032.proved))))
