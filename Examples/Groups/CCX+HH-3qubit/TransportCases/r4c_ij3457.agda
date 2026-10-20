{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4c_ij3457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K3457 ; X47 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00706 as MV00706
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02816 as MV02816
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03028 as MV03028
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 as Base

proved : X57 • K3457 ≈ K3457 • X47
proved = GL.•-cancelʳ {g = X57 • K3457} {g' = K3457 • X47} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV03028.proved (MV00706.proved))) (trans (cong refl Base.proved) (move-product MV00706.proved (MV02816.proved))))
