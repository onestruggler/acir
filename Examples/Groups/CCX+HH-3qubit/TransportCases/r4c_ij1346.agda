{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; X36 ; X46 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00686 as MV00686
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02736 as MV02736
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03008 as MV03008
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X46 • K1346 ≈ K1346 • X36
proved = GL.•-cancelʳ {g = X46 • K1346} {g' = K1346 • X36} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03008.proved (MV00686.proved))) (trans (cong refl Base.proved) (move-product MV00686.proved (MV02736.proved))))
