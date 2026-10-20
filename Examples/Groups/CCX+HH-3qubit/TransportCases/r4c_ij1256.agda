{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij1256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; X26 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02720 as MV02720
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03004 as MV03004
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K1256 ≈ K1256 • X26
proved = GL.•-cancelʳ {g = X56 • K1256} {g' = K1256 • X26} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV03004.proved (MV00682.proved))) (trans (cong refl Base.proved) (move-product MV00682.proved (MV02720.proved))))
