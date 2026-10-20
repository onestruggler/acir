{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij673 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01028 as MV01028
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01029 as MV01029
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X67 • M3 ≈ M3 • X67
proved = GL.•-cancelʳ {g = X67 • M3} {g' = M3 • X67} {h = p (s2 • s1 • s0 • s5 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01028.proved (MV01029.proved))) (trans (cong refl Base.proved) (move-product MV01029.proved (MV01028.proved))))
