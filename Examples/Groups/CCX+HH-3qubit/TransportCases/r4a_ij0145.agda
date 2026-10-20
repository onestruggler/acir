{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij0145 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0145 ; M1 ; M5 ; X01 ; X15 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00649 as MV00649
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02587 as MV02587
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02588 as MV02588
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02589 as MV02589
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02590 as MV02590
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X01 • K0145 ≈ K0145 • X15 • M1 • M5
proved = GL.•-cancelʳ {g = X01 • K0145} {g' = K0145 • X15 • M1 • M5} {h = p (s3 • s2 • s4 • s3)}
  (trans (sym (move-product MV02587.proved (MV00649.proved))) (trans (cong refl Base.proved) (move-product MV00649.proved (move-product MV02588.proved (move-product MV02589.proved (MV02590.proved))))))
