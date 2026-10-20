{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij60137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0137 ; M6 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02254 as MV02254
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02255 as MV02255
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M6 • K0137 ≈ K0137 • M6
proved = GL.•-cancelʳ {g = M6 • K0137} {g' = K0137 • M6} {h = p (s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
  (trans (sym (move-product MV02254.proved (MV02255.proved))) (trans (cong refl Base.proved) (move-product MV02255.proved (MV02254.proved))))
