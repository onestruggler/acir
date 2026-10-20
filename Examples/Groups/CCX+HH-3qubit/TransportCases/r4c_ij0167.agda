{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0167 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; X17 ; X67 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00654 as MV00654
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02608 as MV02608
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02976 as MV02976
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X67 • K0167 ≈ K0167 • X17
proved = GL.•-cancelʳ {g = X67 • K0167} {g' = K0167 • X17} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02976.proved (MV00654.proved))) (trans (cong refl Base.proved) (move-product MV00654.proved (MV02608.proved))))
