{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij172346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2346 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01361 as MV01361
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01362 as MV01362
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K2346 ≈ K2346 • X17
proved = GL.•-cancelʳ {g = X17 • K2346} {g' = K2346 • X17} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
  (trans (sym (move-product MV01361.proved (MV01362.proved))) (trans (cong refl Base.proved) (move-product MV01362.proved (MV01361.proved))))
