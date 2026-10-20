{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij260 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X26 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00890 as MV00890
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00891 as MV00891
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X26 • M0 ≈ M0 • X26
proved = GL.•-cancelʳ {g = X26 • M0} {g' = M0 • X26} {h = p (s1 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV00890.proved (MV00891.proved))) (trans (cong refl Base.proved) (move-product MV00891.proved (MV00890.proved))))
