{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_ij572 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; X57 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01014 as MV01014
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01015 as MV01015
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R085 as Base

proved : X57 • M2 ≈ M2 • X57
proved = GL.•-cancelʳ {g = X57 • M2} {g' = M2 • X57} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)}
  (trans (sym (move-product MV01014.proved (MV01015.proved))) (trans (cong refl Base.proved) (move-product MV01015.proved (MV01014.proved))))
