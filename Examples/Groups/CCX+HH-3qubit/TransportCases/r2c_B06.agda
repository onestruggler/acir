{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B06 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0345 ; K0346 ; K0347 ; K0356 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1345 ; K1346 ; K1347 ; K1356 ; K2345 ; K2346 ; K2347 ; K2356 ; X47 ; X56 ; X57 ; X67 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B045 using (module MV01693 ; module MV01694 ; module MV01695 ; module MV01696 ; module MV01697 ; module MV01698 ; module MV01699 ; module MV01700 ; module MV01701 ; module MV01702 ; module MV01703 ; module MV01704 ; module MV01705 ; module MV01706 ; module MV01707 ; module MV01708 ; module MV01709 ; module MV01710 ; module MV01711 ; module MV01712 ; module MV01713 ; module MV01714 ; module MV01715 ; module MV01716 ; module MV01717 ; module MV01718 ; module MV01719 ; module MV01720 ; module MV01721 ; module MV01722 ; module MV01723 ; module MV01724 ; module MV01725 ; module MV01726 ; module MV01727 ; module MV01728)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B046 using (module MV01729 ; module MV01730 ; module MV01731 ; module MV01732 ; module MV01733 ; module MV01734 ; module MV01735 ; module MV01736 ; module MV01737 ; module MV01738 ; module MV01739 ; module MV01740 ; module MV01741 ; module MV01742 ; module MV01743 ; module MV01744 ; module MV01745 ; module MV01746 ; module MV01747 ; module MV01748 ; module MV01749 ; module MV01750 ; module MV01751 ; module MV01752 ; module MV01753 ; module MV01754 ; module MV01755 ; module MV01756 ; module MV01757 ; module MV01758 ; module MV01759 ; module MV01760 ; module MV01761 ; module MV01762 ; module MV01763 ; module MV01764 ; module MV01765 ; module MV01766 ; module MV01767 ; module MV01768)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01769 ; module MV01770 ; module MV01771 ; module MV01772 ; module MV01773 ; module MV01774 ; module MV01775 ; module MV01776 ; module MV01777 ; module MV01778 ; module MV01779 ; module MV01780 ; module MV01781 ; module MV01782 ; module MV01783 ; module MV01784 ; module MV01785 ; module MV01786 ; module MV01787 ; module MV01788 ; module MV01789 ; module MV01790 ; module MV01791 ; module MV01792 ; module MV01793 ; module MV01794 ; module MV01795 ; module MV01796 ; module MV01797 ; module MV01798 ; module MV01799 ; module MV01800)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R091)

module r2c_ij470235 where

  proved : X47 • K0235 ≈ K0235 • X47
  proved = GL.•-cancelʳ {g = X47 • K0235} {g' = K0235 • X47} {h = p (s1 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01693.proved (MV01694.proved))) (trans (cong refl R091.proved) (move-product MV01694.proved (MV01693.proved))))

module r2c_ij470236 where

  proved : X47 • K0236 ≈ K0236 • X47
  proved = GL.•-cancelʳ {g = X47 • K0236} {g' = K0236 • X47} {h = p (s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01695.proved (MV01696.proved))) (trans (cong refl R091.proved) (move-product MV01696.proved (MV01695.proved))))

module r2c_ij470256 where

  proved : X47 • K0256 ≈ K0256 • X47
  proved = GL.•-cancelʳ {g = X47 • K0256} {g' = K0256 • X47} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01697.proved (MV01698.proved))) (trans (cong refl R091.proved) (move-product MV01698.proved (MV01697.proved))))

module r2c_ij470356 where

  proved : X47 • K0356 ≈ K0356 • X47
  proved = GL.•-cancelʳ {g = X47 • K0356} {g' = K0356 • X47} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01699.proved (MV01700.proved))) (trans (cong refl R091.proved) (move-product MV01700.proved (MV01699.proved))))

module r2c_ij471235 where

  proved : X47 • K1235 ≈ K1235 • X47
  proved = GL.•-cancelʳ {g = X47 • K1235} {g' = K1235 • X47} {h = p (s0 • s1 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01701.proved (MV01702.proved))) (trans (cong refl R091.proved) (move-product MV01702.proved (MV01701.proved))))

module r2c_ij471236 where

  proved : X47 • K1236 ≈ K1236 • X47
  proved = GL.•-cancelʳ {g = X47 • K1236} {g' = K1236 • X47} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01703.proved (MV01704.proved))) (trans (cong refl R091.proved) (move-product MV01704.proved (MV01703.proved))))

module r2c_ij471256 where

  proved : X47 • K1256 ≈ K1256 • X47
  proved = GL.•-cancelʳ {g = X47 • K1256} {g' = K1256 • X47} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01705.proved (MV01706.proved))) (trans (cong refl R091.proved) (move-product MV01706.proved (MV01705.proved))))

module r2c_ij471356 where

  proved : X47 • K1356 ≈ K1356 • X47
  proved = GL.•-cancelʳ {g = X47 • K1356} {g' = K1356 • X47} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01707.proved (MV01708.proved))) (trans (cong refl R091.proved) (move-product MV01708.proved (MV01707.proved))))

module r2c_ij472356 where

  proved : X47 • K2356 ≈ K2356 • X47
  proved = GL.•-cancelʳ {g = X47 • K2356} {g' = K2356 • X47} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01709.proved (MV01710.proved))) (trans (cong refl R091.proved) (move-product MV01710.proved (MV01709.proved))))

module r2c_ij560123 where

  proved : X56 • K0123 ≈ K0123 • X56
  proved = GL.•-cancelʳ {g = X56 • K0123} {g' = K0123 • X56} {h = p (s4 • s5)}
    (trans (sym (move-product MV01711.proved (MV01712.proved))) (trans (cong refl R091.proved) (move-product MV01712.proved (MV01711.proved))))

module r2c_ij560124 where

  proved : X56 • K0124 ≈ K0124 • X56
  proved = GL.•-cancelʳ {g = X56 • K0124} {g' = K0124 • X56} {h = p (s3 • s4 • s5)}
    (trans (sym (move-product MV01713.proved (MV01714.proved))) (trans (cong refl R091.proved) (move-product MV01714.proved (MV01713.proved))))

module r2c_ij560127 where

  proved : X56 • K0127 ≈ K0127 • X56
  proved = GL.•-cancelʳ {g = X56 • K0127} {g' = K0127 • X56} {h = p (s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01715.proved (MV01716.proved))) (trans (cong refl R091.proved) (move-product MV01716.proved (MV01715.proved))))

module r2c_ij560134 where

  proved : X56 • K0134 ≈ K0134 • X56
  proved = GL.•-cancelʳ {g = X56 • K0134} {g' = K0134 • X56} {h = p (s2 • s3 • s4 • s5)}
    (trans (sym (move-product MV01717.proved (MV01718.proved))) (trans (cong refl R091.proved) (move-product MV01718.proved (MV01717.proved))))

module r2c_ij560137 where

  proved : X56 • K0137 ≈ K0137 • X56
  proved = GL.•-cancelʳ {g = X56 • K0137} {g' = K0137 • X56} {h = p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01719.proved (MV01720.proved))) (trans (cong refl R091.proved) (move-product MV01720.proved (MV01719.proved))))

module r2c_ij560147 where

  proved : X56 • K0147 ≈ K0147 • X56
  proved = GL.•-cancelʳ {g = X56 • K0147} {g' = K0147 • X56} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01721.proved (MV01722.proved))) (trans (cong refl R091.proved) (move-product MV01722.proved (MV01721.proved))))

module r2c_ij560234 where

  proved : X56 • K0234 ≈ K0234 • X56
  proved = GL.•-cancelʳ {g = X56 • K0234} {g' = K0234 • X56} {h = p (s1 • s2 • s3 • s4 • s5)}
    (trans (sym (move-product MV01723.proved (MV01724.proved))) (trans (cong refl R091.proved) (move-product MV01724.proved (MV01723.proved))))

module r2c_ij560237 where

  proved : X56 • K0237 ≈ K0237 • X56
  proved = GL.•-cancelʳ {g = X56 • K0237} {g' = K0237 • X56} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01725.proved (MV01726.proved))) (trans (cong refl R091.proved) (move-product MV01726.proved (MV01725.proved))))

module r2c_ij560247 where

  proved : X56 • K0247 ≈ K0247 • X56
  proved = GL.•-cancelʳ {g = X56 • K0247} {g' = K0247 • X56} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01727.proved (MV01728.proved))) (trans (cong refl R091.proved) (move-product MV01728.proved (MV01727.proved))))

module r2c_ij560347 where

  proved : X56 • K0347 ≈ K0347 • X56
  proved = GL.•-cancelʳ {g = X56 • K0347} {g' = K0347 • X56} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01729.proved (MV01730.proved))) (trans (cong refl R091.proved) (move-product MV01730.proved (MV01729.proved))))

module r2c_ij561234 where

  proved : X56 • K1234 ≈ K1234 • X56
  proved = GL.•-cancelʳ {g = X56 • K1234} {g' = K1234 • X56} {h = p (s0 • s1 • s2 • s3 • s4 • s5)}
    (trans (sym (move-product MV01731.proved (MV01732.proved))) (trans (cong refl R091.proved) (move-product MV01732.proved (MV01731.proved))))

module r2c_ij561237 where

  proved : X56 • K1237 ≈ K1237 • X56
  proved = GL.•-cancelʳ {g = X56 • K1237} {g' = K1237 • X56} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01733.proved (MV01734.proved))) (trans (cong refl R091.proved) (move-product MV01734.proved (MV01733.proved))))

module r2c_ij561247 where

  proved : X56 • K1247 ≈ K1247 • X56
  proved = GL.•-cancelʳ {g = X56 • K1247} {g' = K1247 • X56} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01735.proved (MV01736.proved))) (trans (cong refl R091.proved) (move-product MV01736.proved (MV01735.proved))))

module r2c_ij561347 where

  proved : X56 • K1347 ≈ K1347 • X56
  proved = GL.•-cancelʳ {g = X56 • K1347} {g' = K1347 • X56} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01737.proved (MV01738.proved))) (trans (cong refl R091.proved) (move-product MV01738.proved (MV01737.proved))))

module r2c_ij562347 where

  proved : X56 • K2347 ≈ K2347 • X56
  proved = GL.•-cancelʳ {g = X56 • K2347} {g' = K2347 • X56} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01739.proved (MV01740.proved))) (trans (cong refl R091.proved) (move-product MV01740.proved (MV01739.proved))))

module r2c_ij570123 where

  proved : X57 • K0123 ≈ K0123 • X57
  proved = GL.•-cancelʳ {g = X57 • K0123} {g' = K0123 • X57} {h = p (s4 • s6 • s5)}
    (trans (sym (move-product MV01741.proved (MV01742.proved))) (trans (cong refl R091.proved) (move-product MV01742.proved (MV01741.proved))))

module r2c_ij570124 where

  proved : X57 • K0124 ≈ K0124 • X57
  proved = GL.•-cancelʳ {g = X57 • K0124} {g' = K0124 • X57} {h = p (s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01743.proved (MV01744.proved))) (trans (cong refl R091.proved) (move-product MV01744.proved (MV01743.proved))))

module r2c_ij570126 where

  proved : X57 • K0126 ≈ K0126 • X57
  proved = GL.•-cancelʳ {g = X57 • K0126} {g' = K0126 • X57} {h = p (s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01745.proved (MV01746.proved))) (trans (cong refl R091.proved) (move-product MV01746.proved (MV01745.proved))))

module r2c_ij570134 where

  proved : X57 • K0134 ≈ K0134 • X57
  proved = GL.•-cancelʳ {g = X57 • K0134} {g' = K0134 • X57} {h = p (s2 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01747.proved (MV01748.proved))) (trans (cong refl R091.proved) (move-product MV01748.proved (MV01747.proved))))

module r2c_ij570136 where

  proved : X57 • K0136 ≈ K0136 • X57
  proved = GL.•-cancelʳ {g = X57 • K0136} {g' = K0136 • X57} {h = p (s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01749.proved (MV01750.proved))) (trans (cong refl R091.proved) (move-product MV01750.proved (MV01749.proved))))

module r2c_ij570146 where

  proved : X57 • K0146 ≈ K0146 • X57
  proved = GL.•-cancelʳ {g = X57 • K0146} {g' = K0146 • X57} {h = p (s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01751.proved (MV01752.proved))) (trans (cong refl R091.proved) (move-product MV01752.proved (MV01751.proved))))

module r2c_ij570234 where

  proved : X57 • K0234 ≈ K0234 • X57
  proved = GL.•-cancelʳ {g = X57 • K0234} {g' = K0234 • X57} {h = p (s1 • s2 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01753.proved (MV01754.proved))) (trans (cong refl R091.proved) (move-product MV01754.proved (MV01753.proved))))

module r2c_ij570236 where

  proved : X57 • K0236 ≈ K0236 • X57
  proved = GL.•-cancelʳ {g = X57 • K0236} {g' = K0236 • X57} {h = p (s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01755.proved (MV01756.proved))) (trans (cong refl R091.proved) (move-product MV01756.proved (MV01755.proved))))

module r2c_ij570246 where

  proved : X57 • K0246 ≈ K0246 • X57
  proved = GL.•-cancelʳ {g = X57 • K0246} {g' = K0246 • X57} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01757.proved (MV01758.proved))) (trans (cong refl R091.proved) (move-product MV01758.proved (MV01757.proved))))

module r2c_ij570346 where

  proved : X57 • K0346 ≈ K0346 • X57
  proved = GL.•-cancelʳ {g = X57 • K0346} {g' = K0346 • X57} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01759.proved (MV01760.proved))) (trans (cong refl R091.proved) (move-product MV01760.proved (MV01759.proved))))

module r2c_ij571234 where

  proved : X57 • K1234 ≈ K1234 • X57
  proved = GL.•-cancelʳ {g = X57 • K1234} {g' = K1234 • X57} {h = p (s0 • s1 • s2 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01761.proved (MV01762.proved))) (trans (cong refl R091.proved) (move-product MV01762.proved (MV01761.proved))))

module r2c_ij571236 where

  proved : X57 • K1236 ≈ K1236 • X57
  proved = GL.•-cancelʳ {g = X57 • K1236} {g' = K1236 • X57} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01763.proved (MV01764.proved))) (trans (cong refl R091.proved) (move-product MV01764.proved (MV01763.proved))))

module r2c_ij571246 where

  proved : X57 • K1246 ≈ K1246 • X57
  proved = GL.•-cancelʳ {g = X57 • K1246} {g' = K1246 • X57} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01765.proved (MV01766.proved))) (trans (cong refl R091.proved) (move-product MV01766.proved (MV01765.proved))))

module r2c_ij571346 where

  proved : X57 • K1346 ≈ K1346 • X57
  proved = GL.•-cancelʳ {g = X57 • K1346} {g' = K1346 • X57} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01767.proved (MV01768.proved))) (trans (cong refl R091.proved) (move-product MV01768.proved (MV01767.proved))))

module r2c_ij572346 where

  proved : X57 • K2346 ≈ K2346 • X57
  proved = GL.•-cancelʳ {g = X57 • K2346} {g' = K2346 • X57} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01769.proved (MV01770.proved))) (trans (cong refl R091.proved) (move-product MV01770.proved (MV01769.proved))))

module r2c_ij670123 where

  proved : X67 • K0123 ≈ K0123 • X67
  proved = GL.•-cancelʳ {g = X67 • K0123} {g' = K0123 • X67} {h = p (s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01771.proved (MV01772.proved))) (trans (cong refl R091.proved) (move-product MV01772.proved (MV01771.proved))))

module r2c_ij670124 where

  proved : X67 • K0124 ≈ K0124 • X67
  proved = GL.•-cancelʳ {g = X67 • K0124} {g' = K0124 • X67} {h = p (s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01773.proved (MV01774.proved))) (trans (cong refl R091.proved) (move-product MV01774.proved (MV01773.proved))))

module r2c_ij670125 where

  proved : X67 • K0125 ≈ K0125 • X67
  proved = GL.•-cancelʳ {g = X67 • K0125} {g' = K0125 • X67} {h = p (s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01775.proved (MV01776.proved))) (trans (cong refl R091.proved) (move-product MV01776.proved (MV01775.proved))))

module r2c_ij670134 where

  proved : X67 • K0134 ≈ K0134 • X67
  proved = GL.•-cancelʳ {g = X67 • K0134} {g' = K0134 • X67} {h = p (s2 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01777.proved (MV01778.proved))) (trans (cong refl R091.proved) (move-product MV01778.proved (MV01777.proved))))

module r2c_ij670135 where

  proved : X67 • K0135 ≈ K0135 • X67
  proved = GL.•-cancelʳ {g = X67 • K0135} {g' = K0135 • X67} {h = p (s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01779.proved (MV01780.proved))) (trans (cong refl R091.proved) (move-product MV01780.proved (MV01779.proved))))

module r2c_ij670145 where

  proved : X67 • K0145 ≈ K0145 • X67
  proved = GL.•-cancelʳ {g = X67 • K0145} {g' = K0145 • X67} {h = p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01781.proved (MV01782.proved))) (trans (cong refl R091.proved) (move-product MV01782.proved (MV01781.proved))))

module r2c_ij670234 where

  proved : X67 • K0234 ≈ K0234 • X67
  proved = GL.•-cancelʳ {g = X67 • K0234} {g' = K0234 • X67} {h = p (s1 • s2 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01783.proved (MV01784.proved))) (trans (cong refl R091.proved) (move-product MV01784.proved (MV01783.proved))))

module r2c_ij670235 where

  proved : X67 • K0235 ≈ K0235 • X67
  proved = GL.•-cancelʳ {g = X67 • K0235} {g' = K0235 • X67} {h = p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01785.proved (MV01786.proved))) (trans (cong refl R091.proved) (move-product MV01786.proved (MV01785.proved))))

module r2c_ij670245 where

  proved : X67 • K0245 ≈ K0245 • X67
  proved = GL.•-cancelʳ {g = X67 • K0245} {g' = K0245 • X67} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01787.proved (MV01788.proved))) (trans (cong refl R091.proved) (move-product MV01788.proved (MV01787.proved))))

module r2c_ij670345 where

  proved : X67 • K0345 ≈ K0345 • X67
  proved = GL.•-cancelʳ {g = X67 • K0345} {g' = K0345 • X67} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01789.proved (MV01790.proved))) (trans (cong refl R091.proved) (move-product MV01790.proved (MV01789.proved))))

module r2c_ij671234 where

  proved : X67 • K1234 ≈ K1234 • X67
  proved = GL.•-cancelʳ {g = X67 • K1234} {g' = K1234 • X67} {h = p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01791.proved (MV01792.proved))) (trans (cong refl R091.proved) (move-product MV01792.proved (MV01791.proved))))

module r2c_ij671235 where

  proved : X67 • K1235 ≈ K1235 • X67
  proved = GL.•-cancelʳ {g = X67 • K1235} {g' = K1235 • X67} {h = p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01793.proved (MV01794.proved))) (trans (cong refl R091.proved) (move-product MV01794.proved (MV01793.proved))))

module r2c_ij671245 where

  proved : X67 • K1245 ≈ K1245 • X67
  proved = GL.•-cancelʳ {g = X67 • K1245} {g' = K1245 • X67} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01795.proved (MV01796.proved))) (trans (cong refl R091.proved) (move-product MV01796.proved (MV01795.proved))))

module r2c_ij671345 where

  proved : X67 • K1345 ≈ K1345 • X67
  proved = GL.•-cancelʳ {g = X67 • K1345} {g' = K1345 • X67} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01797.proved (MV01798.proved))) (trans (cong refl R091.proved) (move-product MV01798.proved (MV01797.proved))))

module r2c_ij672345 where

  proved : X67 • K2345 ≈ K2345 • X67
  proved = GL.•-cancelʳ {g = X67 • K2345} {g' = K2345 • X67} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01799.proved (MV01800.proved))) (trans (cong refl R091.proved) (move-product MV01800.proved (MV01799.proved))))
