{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4a_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X02 ; X03 ; X04 ; X05 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X24 ; X25 ; X26 ; X27 ; X35 ; X36 ; X37 ; X46 ; X47 ; X57 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R097 as R097
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00010 ; module MV00024)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00058 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00641 ; module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644 ; module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654 ; module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00659 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675 ; module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B065 using (module MV02555 ; module MV02556 ; module MV02557 ; module MV02558 ; module MV02559 ; module MV02560 ; module MV02561 ; module MV02562 ; module MV02563 ; module MV02564 ; module MV02565 ; module MV02566 ; module MV02567 ; module MV02568 ; module MV02569 ; module MV02570 ; module MV02571)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B066 using (module MV02572 ; module MV02573 ; module MV02574 ; module MV02575 ; module MV02576 ; module MV02577 ; module MV02578 ; module MV02579 ; module MV02580 ; module MV02581 ; module MV02582 ; module MV02583 ; module MV02584 ; module MV02585 ; module MV02586 ; module MV02587 ; module MV02588 ; module MV02589 ; module MV02590 ; module MV02591 ; module MV02592 ; module MV02593 ; module MV02594 ; module MV02595 ; module MV02596 ; module MV02597 ; module MV02598 ; module MV02599 ; module MV02600 ; module MV02601 ; module MV02602 ; module MV02603 ; module MV02604 ; module MV02605 ; module MV02606 ; module MV02607 ; module MV02608 ; module MV02609 ; module MV02610 ; module MV02611 ; module MV02612 ; module MV02613 ; module MV02614 ; module MV02615 ; module MV02616 ; module MV02617 ; module MV02618 ; module MV02619 ; module MV02620 ; module MV02621 ; module MV02622 ; module MV02623 ; module MV02624 ; module MV02625 ; module MV02626 ; module MV02627 ; module MV02628 ; module MV02629 ; module MV02630 ; module MV02631 ; module MV02632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B067 using (module MV02633 ; module MV02634 ; module MV02635 ; module MV02636 ; module MV02637 ; module MV02638 ; module MV02639 ; module MV02640 ; module MV02641 ; module MV02642 ; module MV02643 ; module MV02644 ; module MV02645 ; module MV02646 ; module MV02647 ; module MV02648 ; module MV02649 ; module MV02650 ; module MV02651 ; module MV02652 ; module MV02653 ; module MV02654 ; module MV02655 ; module MV02656 ; module MV02657 ; module MV02658 ; module MV02659 ; module MV02660 ; module MV02661 ; module MV02662 ; module MV02663 ; module MV02664 ; module MV02665 ; module MV02666 ; module MV02667 ; module MV02668 ; module MV02669 ; module MV02670 ; module MV02671 ; module MV02672 ; module MV02673 ; module MV02674 ; module MV02675 ; module MV02676)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B068 using (module MV02677 ; module MV02678 ; module MV02679 ; module MV02680 ; module MV02681 ; module MV02682 ; module MV02683 ; module MV02684 ; module MV02685 ; module MV02686 ; module MV02687 ; module MV02688 ; module MV02689 ; module MV02690 ; module MV02691 ; module MV02692 ; module MV02693 ; module MV02694 ; module MV02695 ; module MV02696 ; module MV02697 ; module MV02698 ; module MV02699 ; module MV02700 ; module MV02701 ; module MV02702 ; module MV02703 ; module MV02704 ; module MV02705 ; module MV02706 ; module MV02707 ; module MV02708 ; module MV02709 ; module MV02710 ; module MV02711 ; module MV02712 ; module MV02713 ; module MV02714 ; module MV02715 ; module MV02716 ; module MV02717 ; module MV02718 ; module MV02719 ; module MV02720 ; module MV02721)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B069 using (module MV02722 ; module MV02723 ; module MV02724 ; module MV02725 ; module MV02726 ; module MV02727 ; module MV02728 ; module MV02729 ; module MV02730)

module r4a_ij0123 where

  proved : X01 • K0123 ≈ K0123 • X13 • M1 • M3
  proved = GL.•-cancelʳ {g = X01 • K0123} {g' = K0123 • X13 • M1 • M3} {h = p (ε)}
    (trans (sym (move-product MV02555.proved (MV00641.proved))) (trans (cong refl R097.proved) (move-product MV00641.proved (move-product MV02556.proved (move-product MV02557.proved (MV02558.proved))))))

module r4a_ij0124 where

  proved : X01 • K0124 ≈ K0124 • X14 • M1 • M4
  proved = GL.•-cancelʳ {g = X01 • K0124} {g' = K0124 • X14 • M1 • M4} {h = p (s3)}
    (trans (sym (move-product MV00058.proved (MV00245.proved))) (trans (cong refl R097.proved) (move-product MV00245.proved (move-product MV00113.proved (move-product MV00010.proved (MV00024.proved))))))

module r4a_ij0125 where

  proved : X01 • K0125 ≈ K0125 • X15 • M1 • M5
  proved = GL.•-cancelʳ {g = X01 • K0125} {g' = K0125 • X15 • M1 • M5} {h = p (s4 • s3)}
    (trans (sym (move-product MV02559.proved (MV00642.proved))) (trans (cong refl R097.proved) (move-product MV00642.proved (move-product MV02560.proved (move-product MV02561.proved (MV02562.proved))))))

module r4a_ij0126 where

  proved : X01 • K0126 ≈ K0126 • X16 • M1 • M6
  proved = GL.•-cancelʳ {g = X01 • K0126} {g' = K0126 • X16 • M1 • M6} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV02563.proved (MV00643.proved))) (trans (cong refl R097.proved) (move-product MV00643.proved (move-product MV02564.proved (move-product MV02565.proved (MV02566.proved))))))

module r4a_ij0127 where

  proved : X01 • K0127 ≈ K0127 • X17 • M1 • M7
  proved = GL.•-cancelʳ {g = X01 • K0127} {g' = K0127 • X17 • M1 • M7} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02567.proved (MV00644.proved))) (trans (cong refl R097.proved) (move-product MV00644.proved (move-product MV02568.proved (move-product MV02569.proved (MV02570.proved))))))

module r4a_ij0134 where

  proved : X01 • K0134 ≈ K0134 • X14 • M1 • M4
  proved = GL.•-cancelʳ {g = X01 • K0134} {g' = K0134 • X14 • M1 • M4} {h = p (s2 • s3)}
    (trans (sym (move-product MV02571.proved (MV00645.proved))) (trans (cong refl R097.proved) (move-product MV00645.proved (move-product MV02572.proved (move-product MV02573.proved (MV02574.proved))))))

module r4a_ij0135 where

  proved : X01 • K0135 ≈ K0135 • X15 • M1 • M5
  proved = GL.•-cancelʳ {g = X01 • K0135} {g' = K0135 • X15 • M1 • M5} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV02575.proved (MV00646.proved))) (trans (cong refl R097.proved) (move-product MV00646.proved (move-product MV02576.proved (move-product MV02577.proved (MV02578.proved))))))

module r4a_ij0136 where

  proved : X01 • K0136 ≈ K0136 • X16 • M1 • M6
  proved = GL.•-cancelʳ {g = X01 • K0136} {g' = K0136 • X16 • M1 • M6} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02579.proved (MV00647.proved))) (trans (cong refl R097.proved) (move-product MV00647.proved (move-product MV02580.proved (move-product MV02581.proved (MV02582.proved))))))

module r4a_ij0137 where

  proved : X01 • K0137 ≈ K0137 • X17 • M1 • M7
  proved = GL.•-cancelʳ {g = X01 • K0137} {g' = K0137 • X17 • M1 • M7} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02583.proved (MV00648.proved))) (trans (cong refl R097.proved) (move-product MV00648.proved (move-product MV02584.proved (move-product MV02585.proved (MV02586.proved))))))

module r4a_ij0145 where

  proved : X01 • K0145 ≈ K0145 • X15 • M1 • M5
  proved = GL.•-cancelʳ {g = X01 • K0145} {g' = K0145 • X15 • M1 • M5} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02587.proved (MV00649.proved))) (trans (cong refl R097.proved) (move-product MV00649.proved (move-product MV02588.proved (move-product MV02589.proved (MV02590.proved))))))

module r4a_ij0146 where

  proved : X01 • K0146 ≈ K0146 • X16 • M1 • M6
  proved = GL.•-cancelʳ {g = X01 • K0146} {g' = K0146 • X16 • M1 • M6} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02591.proved (MV00650.proved))) (trans (cong refl R097.proved) (move-product MV00650.proved (move-product MV02592.proved (move-product MV02593.proved (MV02594.proved))))))

module r4a_ij0147 where

  proved : X01 • K0147 ≈ K0147 • X17 • M1 • M7
  proved = GL.•-cancelʳ {g = X01 • K0147} {g' = K0147 • X17 • M1 • M7} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02595.proved (MV00651.proved))) (trans (cong refl R097.proved) (move-product MV00651.proved (move-product MV02596.proved (move-product MV02597.proved (MV02598.proved))))))

module r4a_ij0156 where

  proved : X01 • K0156 ≈ K0156 • X16 • M1 • M6
  proved = GL.•-cancelʳ {g = X01 • K0156} {g' = K0156 • X16 • M1 • M6} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02599.proved (MV00652.proved))) (trans (cong refl R097.proved) (move-product MV00652.proved (move-product MV02600.proved (move-product MV02601.proved (MV02602.proved))))))

module r4a_ij0157 where

  proved : X01 • K0157 ≈ K0157 • X17 • M1 • M7
  proved = GL.•-cancelʳ {g = X01 • K0157} {g' = K0157 • X17 • M1 • M7} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02603.proved (MV00653.proved))) (trans (cong refl R097.proved) (move-product MV00653.proved (move-product MV02604.proved (move-product MV02605.proved (MV02606.proved))))))

module r4a_ij0167 where

  proved : X01 • K0167 ≈ K0167 • X17 • M1 • M7
  proved = GL.•-cancelʳ {g = X01 • K0167} {g' = K0167 • X17 • M1 • M7} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02607.proved (MV00654.proved))) (trans (cong refl R097.proved) (move-product MV00654.proved (move-product MV02608.proved (move-product MV02609.proved (MV02610.proved))))))

module r4a_ij0234 where

  proved : X02 • K0234 ≈ K0234 • X24 • M2 • M4
  proved = GL.•-cancelʳ {g = X02 • K0234} {g' = K0234 • X24 • M2 • M4} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV02611.proved (MV00655.proved))) (trans (cong refl R097.proved) (move-product MV00655.proved (move-product MV02612.proved (move-product MV02613.proved (MV02614.proved))))))

module r4a_ij0235 where

  proved : X02 • K0235 ≈ K0235 • X25 • M2 • M5
  proved = GL.•-cancelʳ {g = X02 • K0235} {g' = K0235 • X25 • M2 • M5} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV02615.proved (MV00656.proved))) (trans (cong refl R097.proved) (move-product MV00656.proved (move-product MV02616.proved (move-product MV02617.proved (MV02618.proved))))))

module r4a_ij0236 where

  proved : X02 • K0236 ≈ K0236 • X26 • M2 • M6
  proved = GL.•-cancelʳ {g = X02 • K0236} {g' = K0236 • X26 • M2 • M6} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02619.proved (MV00657.proved))) (trans (cong refl R097.proved) (move-product MV00657.proved (move-product MV02620.proved (move-product MV02621.proved (MV02622.proved))))))

module r4a_ij0237 where

  proved : X02 • K0237 ≈ K0237 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X02 • K0237} {g' = K0237 • X27 • M2 • M7} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02623.proved (MV00658.proved))) (trans (cong refl R097.proved) (move-product MV00658.proved (move-product MV02624.proved (move-product MV02625.proved (MV02626.proved))))))

module r4a_ij0245 where

  proved : X02 • K0245 ≈ K0245 • X25 • M2 • M5
  proved = GL.•-cancelʳ {g = X02 • K0245} {g' = K0245 • X25 • M2 • M5} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02627.proved (MV00659.proved))) (trans (cong refl R097.proved) (move-product MV00659.proved (move-product MV02628.proved (move-product MV02629.proved (MV02630.proved))))))

module r4a_ij0246 where

  proved : X02 • K0246 ≈ K0246 • X26 • M2 • M6
  proved = GL.•-cancelʳ {g = X02 • K0246} {g' = K0246 • X26 • M2 • M6} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02631.proved (MV00660.proved))) (trans (cong refl R097.proved) (move-product MV00660.proved (move-product MV02632.proved (move-product MV02633.proved (MV02634.proved))))))

module r4a_ij0247 where

  proved : X02 • K0247 ≈ K0247 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X02 • K0247} {g' = K0247 • X27 • M2 • M7} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02635.proved (MV00661.proved))) (trans (cong refl R097.proved) (move-product MV00661.proved (move-product MV02636.proved (move-product MV02637.proved (MV02638.proved))))))

module r4a_ij0256 where

  proved : X02 • K0256 ≈ K0256 • X26 • M2 • M6
  proved = GL.•-cancelʳ {g = X02 • K0256} {g' = K0256 • X26 • M2 • M6} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02639.proved (MV00662.proved))) (trans (cong refl R097.proved) (move-product MV00662.proved (move-product MV02640.proved (move-product MV02641.proved (MV02642.proved))))))

module r4a_ij0257 where

  proved : X02 • K0257 ≈ K0257 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X02 • K0257} {g' = K0257 • X27 • M2 • M7} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02643.proved (MV00663.proved))) (trans (cong refl R097.proved) (move-product MV00663.proved (move-product MV02644.proved (move-product MV02645.proved (MV02646.proved))))))

module r4a_ij0267 where

  proved : X02 • K0267 ≈ K0267 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X02 • K0267} {g' = K0267 • X27 • M2 • M7} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02647.proved (MV00664.proved))) (trans (cong refl R097.proved) (move-product MV00664.proved (move-product MV02648.proved (move-product MV02649.proved (MV02650.proved))))))

module r4a_ij0345 where

  proved : X03 • K0345 ≈ K0345 • X35 • M3 • M5
  proved = GL.•-cancelʳ {g = X03 • K0345} {g' = K0345 • X35 • M3 • M5} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02651.proved (MV00665.proved))) (trans (cong refl R097.proved) (move-product MV00665.proved (move-product MV02652.proved (move-product MV02653.proved (MV02654.proved))))))

module r4a_ij0346 where

  proved : X03 • K0346 ≈ K0346 • X36 • M3 • M6
  proved = GL.•-cancelʳ {g = X03 • K0346} {g' = K0346 • X36 • M3 • M6} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02655.proved (MV00666.proved))) (trans (cong refl R097.proved) (move-product MV00666.proved (move-product MV02656.proved (move-product MV02657.proved (MV02658.proved))))))

module r4a_ij0347 where

  proved : X03 • K0347 ≈ K0347 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X03 • K0347} {g' = K0347 • X37 • M3 • M7} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02659.proved (MV00667.proved))) (trans (cong refl R097.proved) (move-product MV00667.proved (move-product MV02660.proved (move-product MV02661.proved (MV02662.proved))))))

module r4a_ij0356 where

  proved : X03 • K0356 ≈ K0356 • X36 • M3 • M6
  proved = GL.•-cancelʳ {g = X03 • K0356} {g' = K0356 • X36 • M3 • M6} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02663.proved (MV00668.proved))) (trans (cong refl R097.proved) (move-product MV00668.proved (move-product MV02664.proved (move-product MV02665.proved (MV02666.proved))))))

module r4a_ij0357 where

  proved : X03 • K0357 ≈ K0357 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X03 • K0357} {g' = K0357 • X37 • M3 • M7} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02667.proved (MV00669.proved))) (trans (cong refl R097.proved) (move-product MV00669.proved (move-product MV02668.proved (move-product MV02669.proved (MV02670.proved))))))

module r4a_ij0367 where

  proved : X03 • K0367 ≈ K0367 • X37 • M3 • M7
  proved = GL.•-cancelʳ {g = X03 • K0367} {g' = K0367 • X37 • M3 • M7} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02671.proved (MV00670.proved))) (trans (cong refl R097.proved) (move-product MV00670.proved (move-product MV02672.proved (move-product MV02673.proved (MV02674.proved))))))

module r4a_ij0456 where

  proved : X04 • K0456 ≈ K0456 • X46 • M4 • M6
  proved = GL.•-cancelʳ {g = X04 • K0456} {g' = K0456 • X46 • M4 • M6} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02675.proved (MV00671.proved))) (trans (cong refl R097.proved) (move-product MV00671.proved (move-product MV02676.proved (move-product MV02677.proved (MV02678.proved))))))

module r4a_ij0457 where

  proved : X04 • K0457 ≈ K0457 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X04 • K0457} {g' = K0457 • X47 • M4 • M7} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02679.proved (MV00672.proved))) (trans (cong refl R097.proved) (move-product MV00672.proved (move-product MV02680.proved (move-product MV02681.proved (MV02682.proved))))))

module r4a_ij0467 where

  proved : X04 • K0467 ≈ K0467 • X47 • M4 • M7
  proved = GL.•-cancelʳ {g = X04 • K0467} {g' = K0467 • X47 • M4 • M7} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02683.proved (MV00673.proved))) (trans (cong refl R097.proved) (move-product MV00673.proved (move-product MV02684.proved (move-product MV02685.proved (MV02686.proved))))))

module r4a_ij0567 where

  proved : X05 • K0567 ≈ K0567 • X57 • M5 • M7
  proved = GL.•-cancelʳ {g = X05 • K0567} {g' = K0567 • X57 • M5 • M7} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02687.proved (MV00674.proved))) (trans (cong refl R097.proved) (move-product MV00674.proved (move-product MV02688.proved (move-product MV02689.proved (MV02690.proved))))))

module r4a_ij1234 where

  proved : X12 • K1234 ≈ K1234 • X24 • M2 • M4
  proved = GL.•-cancelʳ {g = X12 • K1234} {g' = K1234 • X24 • M2 • M4} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV02691.proved (MV00675.proved))) (trans (cong refl R097.proved) (move-product MV00675.proved (move-product MV02692.proved (move-product MV02693.proved (MV02694.proved))))))

module r4a_ij1235 where

  proved : X12 • K1235 ≈ K1235 • X25 • M2 • M5
  proved = GL.•-cancelʳ {g = X12 • K1235} {g' = K1235 • X25 • M2 • M5} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV02695.proved (MV00676.proved))) (trans (cong refl R097.proved) (move-product MV00676.proved (move-product MV02696.proved (move-product MV02697.proved (MV02698.proved))))))

module r4a_ij1236 where

  proved : X12 • K1236 ≈ K1236 • X26 • M2 • M6
  proved = GL.•-cancelʳ {g = X12 • K1236} {g' = K1236 • X26 • M2 • M6} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02699.proved (MV00677.proved))) (trans (cong refl R097.proved) (move-product MV00677.proved (move-product MV02700.proved (move-product MV02701.proved (MV02702.proved))))))

module r4a_ij1237 where

  proved : X12 • K1237 ≈ K1237 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X12 • K1237} {g' = K1237 • X27 • M2 • M7} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02703.proved (MV00678.proved))) (trans (cong refl R097.proved) (move-product MV00678.proved (move-product MV02704.proved (move-product MV02705.proved (MV02706.proved))))))

module r4a_ij1245 where

  proved : X12 • K1245 ≈ K1245 • X25 • M2 • M5
  proved = GL.•-cancelʳ {g = X12 • K1245} {g' = K1245 • X25 • M2 • M5} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02707.proved (MV00679.proved))) (trans (cong refl R097.proved) (move-product MV00679.proved (move-product MV02708.proved (move-product MV02709.proved (MV02710.proved))))))

module r4a_ij1246 where

  proved : X12 • K1246 ≈ K1246 • X26 • M2 • M6
  proved = GL.•-cancelʳ {g = X12 • K1246} {g' = K1246 • X26 • M2 • M6} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02711.proved (MV00680.proved))) (trans (cong refl R097.proved) (move-product MV00680.proved (move-product MV02712.proved (move-product MV02713.proved (MV02714.proved))))))

module r4a_ij1247 where

  proved : X12 • K1247 ≈ K1247 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X12 • K1247} {g' = K1247 • X27 • M2 • M7} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02715.proved (MV00681.proved))) (trans (cong refl R097.proved) (move-product MV00681.proved (move-product MV02716.proved (move-product MV02717.proved (MV02718.proved))))))

module r4a_ij1256 where

  proved : X12 • K1256 ≈ K1256 • X26 • M2 • M6
  proved = GL.•-cancelʳ {g = X12 • K1256} {g' = K1256 • X26 • M2 • M6} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02719.proved (MV00682.proved))) (trans (cong refl R097.proved) (move-product MV00682.proved (move-product MV02720.proved (move-product MV02721.proved (MV02722.proved))))))

module r4a_ij1257 where

  proved : X12 • K1257 ≈ K1257 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X12 • K1257} {g' = K1257 • X27 • M2 • M7} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02723.proved (MV00683.proved))) (trans (cong refl R097.proved) (move-product MV00683.proved (move-product MV02724.proved (move-product MV02725.proved (MV02726.proved))))))

module r4a_ij1267 where

  proved : X12 • K1267 ≈ K1267 • X27 • M2 • M7
  proved = GL.•-cancelʳ {g = X12 • K1267} {g' = K1267 • X27 • M2 • M7} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02727.proved (MV00684.proved))) (trans (cong refl R097.proved) (move-product MV00684.proved (move-product MV02728.proved (move-product MV02729.proved (MV02730.proved))))))
