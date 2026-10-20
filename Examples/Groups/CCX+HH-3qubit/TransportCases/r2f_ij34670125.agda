{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij34670125 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; K3467 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00707 as MV00707
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02447 as MV02447
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K3467 • K0125 ≈ K0125 • K3467
proved = GL.•-cancelʳ {g = K3467 • K0125} {g' = K0125 • K3467} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00707.proved (MV02447.proved))) (trans (cong refl Base.proved) (move-product MV02447.proved (MV00707.proved))))
