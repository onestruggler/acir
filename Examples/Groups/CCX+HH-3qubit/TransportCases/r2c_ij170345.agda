{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij170345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0345 ; X17 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01351 as MV01351
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01352 as MV01352
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X17 • K0345 ≈ K0345 • X17
proved = GL.•-cancelʳ {g = X17 • K0345} {g' = K0345 • X17} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
  (trans (sym (move-product MV01351.proved (MV01352.proved))) (trans (cong refl Base.proved) (move-product MV01352.proved (MV01351.proved))))
