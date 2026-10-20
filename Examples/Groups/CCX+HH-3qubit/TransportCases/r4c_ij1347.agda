{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1347 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1347 ; X37 ; X47 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00687 as MV00687
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02740 as MV02740
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03009 as MV03009
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X47 • K1347 ≈ K1347 • X37
proved = GL.•-cancelʳ {g = X47 • K1347} {g' = K1347 • X37} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03009.proved (MV00687.proved))) (trans (cong refl Base.proved) (move-product MV00687.proved (MV02740.proved))))
