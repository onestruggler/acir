{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_ij71 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M7 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01889 as MV01889
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01890 as MV01890
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as Base

proved : M7 • M1 ≈ M1 • M7
proved = GL.•-cancelʳ {g = M7 • M1} {g' = M1 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)}
  (trans (sym (move-product MV01889.proved (MV01890.proved))) (trans (cong refl Base.proved) (move-product MV01890.proved (MV01889.proved))))
