{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1567 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00694 as MV00694
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02768 as MV02768
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03016 as MV03016
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K1567 ≈ K1567 • X57
proved = GL.•-cancelʳ {g = X67 • K1567} {g' = K1567 • X57} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03016.proved (MV00694.proved))) (trans (cong refl Base.proved) (move-product MV00694.proved (MV02768.proved))))
