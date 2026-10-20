{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1346 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1346 ; M3 ; M6 ; X13 ; X36 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00686 as MV00686
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02735 as MV02735
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02736 as MV02736
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02737 as MV02737
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02738 as MV02738
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X13 • K1346 ≈ K1346 • X36 • M3 • M6
proved = GL.•-cancelʳ {g = X13 • K1346} {g' = K1346 • X36 • M3 • M6} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02735.proved (MV00686.proved))) (trans (cong refl Base.proved) (move-product MV00686.proved (move-product MV02736.proved (move-product MV02737.proved (MV02738.proved))))))
