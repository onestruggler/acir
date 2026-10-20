{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_ij2357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2357 ; M3 ; M7 ; X23 ; X37 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00699 as MV00699
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02787 as MV02787
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02788 as MV02788
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02789 as MV02789
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02790 as MV02790
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as Base

proved : X23 • K2357 ≈ K2357 • X37 • M3 • M7
proved = GL.•-cancelʳ {g = X23 • K2357} {g' = K2357 • X37 • M3 • M7} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV02787.proved (MV00699.proved))) (trans (cong refl Base.proved) (move-product MV00699.proved (move-product MV02788.proved (move-product MV02789.proved (MV02790.proved))))))
