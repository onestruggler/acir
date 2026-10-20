{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij1256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1256 ; M2 ; M6 ; X12 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00682 as MV00682
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02719 as MV02719
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02720 as MV02720
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02721 as MV02721
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02722 as MV02722
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X12 • K1256 ≈ K1256 • X26 • M2 • M6
proved = GL.•-cancelʳ {g = X12 • K1256} {g' = K1256 • X26 • M2 • M6} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02719.proved (MV00682.proved))) (trans (cong refl Base.proved) (move-product MV00682.proved (move-product MV02720.proved (move-product MV02721.proved (MV02722.proved))))))
