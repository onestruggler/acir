{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij0256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0256 ; X26 ; X56 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00662 as MV00662
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02640 as MV02640
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02984 as MV02984
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X56 • K0256 ≈ K0256 • X26
proved = GL.•-cancelʳ {g = X56 • K0256} {g' = K0256 • X26} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
  (trans (sym (move-product MV02984.proved (MV00662.proved))) (trans (cong refl Base.proved) (move-product MV00662.proved (MV02640.proved))))
