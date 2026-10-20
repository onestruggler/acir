{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij573 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01016 as MV01016
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01017 as MV01017
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X57 • M3 ≈ M3 • X57
proved = GL.•-cancelʳ {g = X57 • M3} {g' = M3 • X57} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01016.proved (MV01017.proved))) (trans (cong refl Base.proved) (move-product MV01017.proved (MV01016.proved))))
