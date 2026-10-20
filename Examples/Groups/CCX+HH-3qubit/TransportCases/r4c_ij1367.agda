{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; X37 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00690 as MV00690
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02752 as MV02752
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03012 as MV03012
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K1367 ≈ K1367 • X37
proved = GL.•-cancelʳ {g = X67 • K1367} {g' = K1367 • X37} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03012.proved (MV00690.proved))) (trans (cong refl Base.proved) (move-product MV00690.proved (MV02752.proved))))
