{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_ij02671345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0267 ; K1345 ; _•_ ; _≈_ ; cong ; move-product ; p ; refl ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; module GL)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00664 as MV00664
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02404 as MV02404
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as Base

proved : K0267 • K1345 ≈ K1345 • K0267
proved = GL.•-cancelʳ {g = K0267 • K1345} {g' = K1345 • K0267} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
  (trans (sym (move-product MV00664.proved (MV02404.proved))) (trans (cong refl Base.proved) (move-product MV02404.proved (MV00664.proved))))
