{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_ij12467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K2467 ; M1 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01969 as MV01969
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01970 as MV01970
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as Base

proved : M1 • K2467 ≈ K2467 • M1
proved = GL.•-cancelʳ {g = M1 • K2467} {g' = K2467 • M1} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
  (trans (sym (move-product MV01969.proved (MV01970.proved))) (trans (cong refl Base.proved) (move-product MV01970.proved (MV01969.proved))))
