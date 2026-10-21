{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B063 using (module MV02441 ; module MV02442 ; module MV02443)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B064 using (module MV02444 ; module MV02445 ; module MV02446 ; module MV02447 ; module MV02448 ; module MV02449)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R096)

module r2f_ij24560137 where

  proved : K2456 • K0137 ≈ K0137 • K2456
  proved = GL.•-cancelʳ {g = K2456 • K0137} {g' = K0137 • K2456} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00701.proved (MV02441.proved))) (trans (cong refl R096.proved) (move-product MV02441.proved (MV00701.proved))))

module r2f_ij24570136 where

  proved : K2457 • K0136 ≈ K0136 • K2457
  proved = GL.•-cancelʳ {g = K2457 • K0136} {g' = K0136 • K2457} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00702.proved (MV02442.proved))) (trans (cong refl R096.proved) (move-product MV02442.proved (MV00702.proved))))

module r2f_ij24670135 where

  proved : K2467 • K0135 ≈ K0135 • K2467
  proved = GL.•-cancelʳ {g = K2467 • K0135} {g' = K0135 • K2467} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00703.proved (MV02443.proved))) (trans (cong refl R096.proved) (move-product MV02443.proved (MV00703.proved))))

module r2f_ij25670134 where

  proved : K2567 • K0134 ≈ K0134 • K2567
  proved = GL.•-cancelʳ {g = K2567 • K0134} {g' = K0134 • K2567} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00704.proved (MV02444.proved))) (trans (cong refl R096.proved) (move-product MV02444.proved (MV00704.proved))))

module r2f_ij34560127 where

  proved : K3456 • K0127 ≈ K0127 • K3456
  proved = GL.•-cancelʳ {g = K3456 • K0127} {g' = K0127 • K3456} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00705.proved (MV02445.proved))) (trans (cong refl R096.proved) (move-product MV02445.proved (MV00705.proved))))

module r2f_ij34570126 where

  proved : K3457 • K0126 ≈ K0126 • K3457
  proved = GL.•-cancelʳ {g = K3457 • K0126} {g' = K0126 • K3457} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00706.proved (MV02446.proved))) (trans (cong refl R096.proved) (move-product MV02446.proved (MV00706.proved))))

module r2f_ij34670125 where

  proved : K3467 • K0125 ≈ K0125 • K3467
  proved = GL.•-cancelʳ {g = K3467 • K0125} {g' = K0125 • K3467} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00707.proved (MV02447.proved))) (trans (cong refl R096.proved) (move-product MV02447.proved (MV00707.proved))))

module r2f_ij35670124 where

  proved : K3567 • K0124 ≈ K0124 • K3567
  proved = GL.•-cancelʳ {g = K3567 • K0124} {g' = K0124 • K3567} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00708.proved (MV02448.proved))) (trans (cong refl R096.proved) (move-product MV02448.proved (MV00708.proved))))

module r2f_ij45670123 where

  proved : K4567 • K0123 ≈ K0123 • K4567
  proved = GL.•-cancelʳ {g = K4567 • K0123} {g' = K0123 • K4567} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00632.proved (MV02449.proved))) (trans (cong refl R096.proved) (move-product MV02449.proved (MV00632.proved))))
