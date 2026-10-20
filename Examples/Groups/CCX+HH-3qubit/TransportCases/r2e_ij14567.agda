{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij14567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K4567 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01981 as MV01981
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01982 as MV01982
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K4567 ≈ K4567 • M1
proved = GL.•-cancelʳ {g = M1 • K4567} {g' = K4567 • M1} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01981.proved (MV01982.proved))) (trans (cong refl Base.proved) (move-product MV01982.proved (MV01981.proved))))
