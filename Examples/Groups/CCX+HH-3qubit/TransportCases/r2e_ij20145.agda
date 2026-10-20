{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij20145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; M2 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01986 as MV01986
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M2 • K0145 ≈ K0145 • M2
proved = GL.•-cancelʳ {g = M2 • K0145} {g' = K0145 • M2} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV01986.proved (MV00649.proved))) (trans (cong refl Base.proved) (move-product MV00649.proved (MV01986.proved))))
