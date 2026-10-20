{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_ij230456 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0456 ; X23 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01375 as MV01375
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01376 as MV01376
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as Base

proved : X23 • K0456 ≈ K0456 • X23
proved = GL.•-cancelʳ {g = X23 • K0456} {g' = K0456 • X23} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
  (trans (sym (move-product MV01375.proved (MV01376.proved))) (trans (cong refl Base.proved) (move-product MV01376.proved (MV01375.proved))))
