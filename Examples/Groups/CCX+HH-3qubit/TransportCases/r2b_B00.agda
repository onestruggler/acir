{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2b_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00002 ; module MV00630)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00104 ; module MV00105)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00635 ; module MV00636 ; module MV00637 ; module MV00638 ; module MV00639 ; module MV00640)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00709 ; module MV00710 ; module MV00711 ; module MV00712 ; module MV00713 ; module MV00714 ; module MV00715 ; module MV00716 ; module MV00717 ; module MV00718 ; module MV00719 ; module MV00720 ; module MV00721 ; module MV00722 ; module MV00723 ; module MV00724 ; module MV00725 ; module MV00726 ; module MV00727 ; module MV00728 ; module MV00729 ; module MV00730 ; module MV00731 ; module MV00732 ; module MV00733 ; module MV00734)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B019 using (module MV00735 ; module MV00736 ; module MV00737 ; module MV00738 ; module MV00739 ; module MV00740 ; module MV00741 ; module MV00742 ; module MV00743 ; module MV00744 ; module MV00745 ; module MV00746 ; module MV00747 ; module MV00748 ; module MV00749 ; module MV00750 ; module MV00751 ; module MV00752 ; module MV00753 ; module MV00754 ; module MV00755 ; module MV00756 ; module MV00757 ; module MV00758 ; module MV00759 ; module MV00760 ; module MV00761 ; module MV00762 ; module MV00763 ; module MV00764 ; module MV00765 ; module MV00766 ; module MV00767 ; module MV00768 ; module MV00769 ; module MV00770 ; module MV00771 ; module MV00772 ; module MV00773 ; module MV00774 ; module MV00775 ; module MV00776 ; module MV00777 ; module MV00778 ; module MV00779 ; module MV00780)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B020 using (module MV00781 ; module MV00782 ; module MV00783 ; module MV00784 ; module MV00785 ; module MV00786 ; module MV00787 ; module MV00788 ; module MV00789 ; module MV00790 ; module MV00791 ; module MV00792 ; module MV00793 ; module MV00794 ; module MV00795 ; module MV00796 ; module MV00797 ; module MV00798 ; module MV00799 ; module MV00800 ; module MV00801 ; module MV00802 ; module MV00803 ; module MV00804 ; module MV00805 ; module MV00806 ; module MV00807 ; module MV00808 ; module MV00809 ; module MV00810 ; module MV00811 ; module MV00812 ; module MV00813 ; module MV00814 ; module MV00815 ; module MV00816 ; module MV00817 ; module MV00818 ; module MV00819 ; module MV00820 ; module MV00821 ; module MV00822 ; module MV00823 ; module MV00824 ; module MV00825)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R085)

module r2b_ij012 where

  proved : X01 • M2 ≈ M2 • X01
  proved = GL.•-cancelʳ {g = X01 • M2} {g' = M2 • X01} {h = p (s1 • s0)}
    (trans (sym (move-product MV00709.proved (MV00636.proved))) (trans (cong refl R085.proved) (move-product MV00636.proved (MV00709.proved))))

module r2b_ij013 where

  proved : X01 • M3 ≈ M3 • X01
  proved = GL.•-cancelʳ {g = X01 • M3} {g' = M3 • X01} {h = p (s2 • s1 • s0)}
    (trans (sym (move-product MV00710.proved (MV00630.proved))) (trans (cong refl R085.proved) (move-product MV00630.proved (MV00710.proved))))

module r2b_ij014 where

  proved : X01 • M4 ≈ M4 • X01
  proved = GL.•-cancelʳ {g = X01 • M4} {g' = M4 • X01} {h = p (s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00711.proved (MV00637.proved))) (trans (cong refl R085.proved) (move-product MV00637.proved (MV00711.proved))))

module r2b_ij015 where

  proved : X01 • M5 ≈ M5 • X01
  proved = GL.•-cancelʳ {g = X01 • M5} {g' = M5 • X01} {h = p (s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00712.proved (MV00638.proved))) (trans (cong refl R085.proved) (move-product MV00638.proved (MV00712.proved))))

module r2b_ij016 where

  proved : X01 • M6 ≈ M6 • X01
  proved = GL.•-cancelʳ {g = X01 • M6} {g' = M6 • X01} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00713.proved (MV00639.proved))) (trans (cong refl R085.proved) (move-product MV00639.proved (MV00713.proved))))

module r2b_ij017 where

  proved : X01 • M7 ≈ M7 • X01
  proved = GL.•-cancelʳ {g = X01 • M7} {g' = M7 • X01} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00714.proved (MV00640.proved))) (trans (cong refl R085.proved) (move-product MV00640.proved (MV00714.proved))))

module r2b_ij021 where

  proved : X02 • M1 ≈ M1 • X02
  proved = GL.•-cancelʳ {g = X02 • M1} {g' = M1 • X02} {h = p (s0)}
    (trans (sym (move-product MV00104.proved (MV00000.proved))) (trans (cong refl R085.proved) (move-product MV00000.proved (MV00104.proved))))

module r2b_ij023 where

  proved : X02 • M3 ≈ M3 • X02
  proved = GL.•-cancelʳ {g = X02 • M3} {g' = M3 • X02} {h = p (s2 • s1 • s0 • s2)}
    (trans (sym (move-product MV00715.proved (MV00716.proved))) (trans (cong refl R085.proved) (move-product MV00716.proved (MV00715.proved))))

module r2b_ij024 where

  proved : X02 • M4 ≈ M4 • X02
  proved = GL.•-cancelʳ {g = X02 • M4} {g' = M4 • X02} {h = p (s3 • s2 • s1 • s0 • s2)}
    (trans (sym (move-product MV00717.proved (MV00718.proved))) (trans (cong refl R085.proved) (move-product MV00718.proved (MV00717.proved))))

module r2b_ij025 where

  proved : X02 • M5 ≈ M5 • X02
  proved = GL.•-cancelʳ {g = X02 • M5} {g' = M5 • X02} {h = p (s4 • s3 • s2 • s1 • s0 • s2)}
    (trans (sym (move-product MV00719.proved (MV00720.proved))) (trans (cong refl R085.proved) (move-product MV00720.proved (MV00719.proved))))

module r2b_ij026 where

  proved : X02 • M6 ≈ M6 • X02
  proved = GL.•-cancelʳ {g = X02 • M6} {g' = M6 • X02} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2)}
    (trans (sym (move-product MV00721.proved (MV00722.proved))) (trans (cong refl R085.proved) (move-product MV00722.proved (MV00721.proved))))

module r2b_ij027 where

  proved : X02 • M7 ≈ M7 • X02
  proved = GL.•-cancelʳ {g = X02 • M7} {g' = M7 • X02} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2)}
    (trans (sym (move-product MV00723.proved (MV00724.proved))) (trans (cong refl R085.proved) (move-product MV00724.proved (MV00723.proved))))

module r2b_ij031 where

  proved : X03 • M1 ≈ M1 • X03
  proved = GL.•-cancelʳ {g = X03 • M1} {g' = M1 • X03} {h = p (s0 • s2)}
    (trans (sym (move-product MV00725.proved (MV00726.proved))) (trans (cong refl R085.proved) (move-product MV00726.proved (MV00725.proved))))

module r2b_ij032 where

  proved : X03 • M2 ≈ M2 • X03
  proved = GL.•-cancelʳ {g = X03 • M2} {g' = M2 • X03} {h = p (s1 • s0 • s2)}
    (trans (sym (move-product MV00727.proved (MV00728.proved))) (trans (cong refl R085.proved) (move-product MV00728.proved (MV00727.proved))))

module r2b_ij034 where

  proved : X03 • M4 ≈ M4 • X03
  proved = GL.•-cancelʳ {g = X03 • M4} {g' = M4 • X03} {h = p (s3 • s2 • s1 • s0 • s3 • s2)}
    (trans (sym (move-product MV00729.proved (MV00730.proved))) (trans (cong refl R085.proved) (move-product MV00730.proved (MV00729.proved))))

module r2b_ij035 where

  proved : X03 • M5 ≈ M5 • X03
  proved = GL.•-cancelʳ {g = X03 • M5} {g' = M5 • X03} {h = p (s4 • s3 • s2 • s1 • s0 • s3 • s2)}
    (trans (sym (move-product MV00731.proved (MV00732.proved))) (trans (cong refl R085.proved) (move-product MV00732.proved (MV00731.proved))))

module r2b_ij036 where

  proved : X03 • M6 ≈ M6 • X03
  proved = GL.•-cancelʳ {g = X03 • M6} {g' = M6 • X03} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)}
    (trans (sym (move-product MV00733.proved (MV00734.proved))) (trans (cong refl R085.proved) (move-product MV00734.proved (MV00733.proved))))

module r2b_ij037 where

  proved : X03 • M7 ≈ M7 • X03
  proved = GL.•-cancelʳ {g = X03 • M7} {g' = M7 • X03} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)}
    (trans (sym (move-product MV00735.proved (MV00736.proved))) (trans (cong refl R085.proved) (move-product MV00736.proved (MV00735.proved))))

module r2b_ij041 where

  proved : X04 • M1 ≈ M1 • X04
  proved = GL.•-cancelʳ {g = X04 • M1} {g' = M1 • X04} {h = p (s0 • s3 • s2)}
    (trans (sym (move-product MV00737.proved (MV00738.proved))) (trans (cong refl R085.proved) (move-product MV00738.proved (MV00737.proved))))

module r2b_ij042 where

  proved : X04 • M2 ≈ M2 • X04
  proved = GL.•-cancelʳ {g = X04 • M2} {g' = M2 • X04} {h = p (s1 • s0 • s3 • s2)}
    (trans (sym (move-product MV00739.proved (MV00740.proved))) (trans (cong refl R085.proved) (move-product MV00740.proved (MV00739.proved))))

module r2b_ij043 where

  proved : X04 • M3 ≈ M3 • X04
  proved = GL.•-cancelʳ {g = X04 • M3} {g' = M3 • X04} {h = p (s2 • s1 • s0 • s3 • s2)}
    (trans (sym (move-product MV00741.proved (MV00742.proved))) (trans (cong refl R085.proved) (move-product MV00742.proved (MV00741.proved))))

module r2b_ij045 where

  proved : X04 • M5 ≈ M5 • X04
  proved = GL.•-cancelʳ {g = X04 • M5} {g' = M5 • X04} {h = p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00743.proved (MV00744.proved))) (trans (cong refl R085.proved) (move-product MV00744.proved (MV00743.proved))))

module r2b_ij046 where

  proved : X04 • M6 ≈ M6 • X04
  proved = GL.•-cancelʳ {g = X04 • M6} {g' = M6 • X04} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00745.proved (MV00746.proved))) (trans (cong refl R085.proved) (move-product MV00746.proved (MV00745.proved))))

module r2b_ij047 where

  proved : X04 • M7 ≈ M7 • X04
  proved = GL.•-cancelʳ {g = X04 • M7} {g' = M7 • X04} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00747.proved (MV00748.proved))) (trans (cong refl R085.proved) (move-product MV00748.proved (MV00747.proved))))

module r2b_ij051 where

  proved : X05 • M1 ≈ M1 • X05
  proved = GL.•-cancelʳ {g = X05 • M1} {g' = M1 • X05} {h = p (s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00749.proved (MV00750.proved))) (trans (cong refl R085.proved) (move-product MV00750.proved (MV00749.proved))))

module r2b_ij052 where

  proved : X05 • M2 ≈ M2 • X05
  proved = GL.•-cancelʳ {g = X05 • M2} {g' = M2 • X05} {h = p (s1 • s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00751.proved (MV00752.proved))) (trans (cong refl R085.proved) (move-product MV00752.proved (MV00751.proved))))

module r2b_ij053 where

  proved : X05 • M3 ≈ M3 • X05
  proved = GL.•-cancelʳ {g = X05 • M3} {g' = M3 • X05} {h = p (s2 • s1 • s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00753.proved (MV00754.proved))) (trans (cong refl R085.proved) (move-product MV00754.proved (MV00753.proved))))

module r2b_ij054 where

  proved : X05 • M4 ≈ M4 • X05
  proved = GL.•-cancelʳ {g = X05 • M4} {g' = M4 • X05} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2)}
    (trans (sym (move-product MV00755.proved (MV00756.proved))) (trans (cong refl R085.proved) (move-product MV00756.proved (MV00755.proved))))

module r2b_ij056 where

  proved : X05 • M6 ≈ M6 • X05
  proved = GL.•-cancelʳ {g = X05 • M6} {g' = M6 • X05} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00757.proved (MV00758.proved))) (trans (cong refl R085.proved) (move-product MV00758.proved (MV00757.proved))))

module r2b_ij057 where

  proved : X05 • M7 ≈ M7 • X05
  proved = GL.•-cancelʳ {g = X05 • M7} {g' = M7 • X05} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00759.proved (MV00760.proved))) (trans (cong refl R085.proved) (move-product MV00760.proved (MV00759.proved))))

module r2b_ij061 where

  proved : X06 • M1 ≈ M1 • X06
  proved = GL.•-cancelʳ {g = X06 • M1} {g' = M1 • X06} {h = p (s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00761.proved (MV00762.proved))) (trans (cong refl R085.proved) (move-product MV00762.proved (MV00761.proved))))

module r2b_ij062 where

  proved : X06 • M2 ≈ M2 • X06
  proved = GL.•-cancelʳ {g = X06 • M2} {g' = M2 • X06} {h = p (s1 • s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00763.proved (MV00764.proved))) (trans (cong refl R085.proved) (move-product MV00764.proved (MV00763.proved))))

module r2b_ij063 where

  proved : X06 • M3 ≈ M3 • X06
  proved = GL.•-cancelʳ {g = X06 • M3} {g' = M3 • X06} {h = p (s2 • s1 • s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00765.proved (MV00766.proved))) (trans (cong refl R085.proved) (move-product MV00766.proved (MV00765.proved))))

module r2b_ij064 where

  proved : X06 • M4 ≈ M4 • X06
  proved = GL.•-cancelʳ {g = X06 • M4} {g' = M4 • X06} {h = p (s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00767.proved (MV00768.proved))) (trans (cong refl R085.proved) (move-product MV00768.proved (MV00767.proved))))

module r2b_ij065 where

  proved : X06 • M5 ≈ M5 • X06
  proved = GL.•-cancelʳ {g = X06 • M5} {g' = M5 • X06} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00769.proved (MV00770.proved))) (trans (cong refl R085.proved) (move-product MV00770.proved (MV00769.proved))))

module r2b_ij067 where

  proved : X06 • M7 ≈ M7 • X06
  proved = GL.•-cancelʳ {g = X06 • M7} {g' = M7 • X06} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00771.proved (MV00772.proved))) (trans (cong refl R085.proved) (move-product MV00772.proved (MV00771.proved))))

module r2b_ij071 where

  proved : X07 • M1 ≈ M1 • X07
  proved = GL.•-cancelʳ {g = X07 • M1} {g' = M1 • X07} {h = p (s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00773.proved (MV00774.proved))) (trans (cong refl R085.proved) (move-product MV00774.proved (MV00773.proved))))

module r2b_ij072 where

  proved : X07 • M2 ≈ M2 • X07
  proved = GL.•-cancelʳ {g = X07 • M2} {g' = M2 • X07} {h = p (s1 • s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00775.proved (MV00776.proved))) (trans (cong refl R085.proved) (move-product MV00776.proved (MV00775.proved))))

module r2b_ij073 where

  proved : X07 • M3 ≈ M3 • X07
  proved = GL.•-cancelʳ {g = X07 • M3} {g' = M3 • X07} {h = p (s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00777.proved (MV00778.proved))) (trans (cong refl R085.proved) (move-product MV00778.proved (MV00777.proved))))

module r2b_ij074 where

  proved : X07 • M4 ≈ M4 • X07
  proved = GL.•-cancelʳ {g = X07 • M4} {g' = M4 • X07} {h = p (s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00779.proved (MV00780.proved))) (trans (cong refl R085.proved) (move-product MV00780.proved (MV00779.proved))))

module r2b_ij075 where

  proved : X07 • M5 ≈ M5 • X07
  proved = GL.•-cancelʳ {g = X07 • M5} {g' = M5 • X07} {h = p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00781.proved (MV00782.proved))) (trans (cong refl R085.proved) (move-product MV00782.proved (MV00781.proved))))

module r2b_ij076 where

  proved : X07 • M6 ≈ M6 • X07
  proved = GL.•-cancelʳ {g = X07 • M6} {g' = M6 • X07} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4 • s3 • s2)}
    (trans (sym (move-product MV00783.proved (MV00784.proved))) (trans (cong refl R085.proved) (move-product MV00784.proved (MV00783.proved))))

module r2b_ij120 where

  proved : X12 • M0 ≈ M0 • X12
  proved = GL.•-cancelʳ {g = X12 • M0} {g' = M0 • X12} {h = p (ε)}
    (trans (sym (move-product MV00785.proved (MV00635.proved))) (trans (cong refl R085.proved) (move-product MV00635.proved (MV00785.proved))))

module r2b_ij123 where

  proved : X12 • M3 ≈ M3 • X12
  proved = GL.•-cancelʳ {g = X12 • M3} {g' = M3 • X12} {h = p (s2 • s1 • s0 • s1 • s2)}
    (trans (sym (move-product MV00786.proved (MV00787.proved))) (trans (cong refl R085.proved) (move-product MV00787.proved (MV00786.proved))))

module r2b_ij124 where

  proved : X12 • M4 ≈ M4 • X12
  proved = GL.•-cancelʳ {g = X12 • M4} {g' = M4 • X12} {h = p (s3 • s2 • s1 • s0 • s1 • s2)}
    (trans (sym (move-product MV00788.proved (MV00789.proved))) (trans (cong refl R085.proved) (move-product MV00789.proved (MV00788.proved))))

module r2b_ij125 where

  proved : X12 • M5 ≈ M5 • X12
  proved = GL.•-cancelʳ {g = X12 • M5} {g' = M5 • X12} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s2)}
    (trans (sym (move-product MV00790.proved (MV00791.proved))) (trans (cong refl R085.proved) (move-product MV00791.proved (MV00790.proved))))

module r2b_ij126 where

  proved : X12 • M6 ≈ M6 • X12
  proved = GL.•-cancelʳ {g = X12 • M6} {g' = M6 • X12} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)}
    (trans (sym (move-product MV00792.proved (MV00793.proved))) (trans (cong refl R085.proved) (move-product MV00793.proved (MV00792.proved))))

module r2b_ij127 where

  proved : X12 • M7 ≈ M7 • X12
  proved = GL.•-cancelʳ {g = X12 • M7} {g' = M7 • X12} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2)}
    (trans (sym (move-product MV00794.proved (MV00795.proved))) (trans (cong refl R085.proved) (move-product MV00795.proved (MV00794.proved))))

module r2b_ij130 where

  proved : X13 • M0 ≈ M0 • X13
  proved = GL.•-cancelʳ {g = X13 • M0} {g' = M0 • X13} {h = p (s2)}
    (trans (sym (move-product MV00105.proved (MV00002.proved))) (trans (cong refl R085.proved) (move-product MV00002.proved (MV00105.proved))))

module r2b_ij132 where

  proved : X13 • M2 ≈ M2 • X13
  proved = GL.•-cancelʳ {g = X13 • M2} {g' = M2 • X13} {h = p (s1 • s0 • s1 • s2)}
    (trans (sym (move-product MV00796.proved (MV00797.proved))) (trans (cong refl R085.proved) (move-product MV00797.proved (MV00796.proved))))

module r2b_ij134 where

  proved : X13 • M4 ≈ M4 • X13
  proved = GL.•-cancelʳ {g = X13 • M4} {g' = M4 • X13} {h = p (s3 • s2 • s1 • s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00798.proved (MV00799.proved))) (trans (cong refl R085.proved) (move-product MV00799.proved (MV00798.proved))))

module r2b_ij135 where

  proved : X13 • M5 ≈ M5 • X13
  proved = GL.•-cancelʳ {g = X13 • M5} {g' = M5 • X13} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00800.proved (MV00801.proved))) (trans (cong refl R085.proved) (move-product MV00801.proved (MV00800.proved))))

module r2b_ij136 where

  proved : X13 • M6 ≈ M6 • X13
  proved = GL.•-cancelʳ {g = X13 • M6} {g' = M6 • X13} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00802.proved (MV00803.proved))) (trans (cong refl R085.proved) (move-product MV00803.proved (MV00802.proved))))

module r2b_ij137 where

  proved : X13 • M7 ≈ M7 • X13
  proved = GL.•-cancelʳ {g = X13 • M7} {g' = M7 • X13} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00804.proved (MV00805.proved))) (trans (cong refl R085.proved) (move-product MV00805.proved (MV00804.proved))))

module r2b_ij140 where

  proved : X14 • M0 ≈ M0 • X14
  proved = GL.•-cancelʳ {g = X14 • M0} {g' = M0 • X14} {h = p (s3 • s2)}
    (trans (sym (move-product MV00806.proved (MV00807.proved))) (trans (cong refl R085.proved) (move-product MV00807.proved (MV00806.proved))))

module r2b_ij142 where

  proved : X14 • M2 ≈ M2 • X14
  proved = GL.•-cancelʳ {g = X14 • M2} {g' = M2 • X14} {h = p (s1 • s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00808.proved (MV00809.proved))) (trans (cong refl R085.proved) (move-product MV00809.proved (MV00808.proved))))

module r2b_ij143 where

  proved : X14 • M3 ≈ M3 • X14
  proved = GL.•-cancelʳ {g = X14 • M3} {g' = M3 • X14} {h = p (s2 • s1 • s0 • s1 • s3 • s2)}
    (trans (sym (move-product MV00810.proved (MV00811.proved))) (trans (cong refl R085.proved) (move-product MV00811.proved (MV00810.proved))))

module r2b_ij145 where

  proved : X14 • M5 ≈ M5 • X14
  proved = GL.•-cancelʳ {g = X14 • M5} {g' = M5 • X14} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00812.proved (MV00813.proved))) (trans (cong refl R085.proved) (move-product MV00813.proved (MV00812.proved))))

module r2b_ij146 where

  proved : X14 • M6 ≈ M6 • X14
  proved = GL.•-cancelʳ {g = X14 • M6} {g' = M6 • X14} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00814.proved (MV00815.proved))) (trans (cong refl R085.proved) (move-product MV00815.proved (MV00814.proved))))

module r2b_ij147 where

  proved : X14 • M7 ≈ M7 • X14
  proved = GL.•-cancelʳ {g = X14 • M7} {g' = M7 • X14} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00816.proved (MV00817.proved))) (trans (cong refl R085.proved) (move-product MV00817.proved (MV00816.proved))))

module r2b_ij150 where

  proved : X15 • M0 ≈ M0 • X15
  proved = GL.•-cancelʳ {g = X15 • M0} {g' = M0 • X15} {h = p (s4 • s3 • s2)}
    (trans (sym (move-product MV00818.proved (MV00819.proved))) (trans (cong refl R085.proved) (move-product MV00819.proved (MV00818.proved))))

module r2b_ij152 where

  proved : X15 • M2 ≈ M2 • X15
  proved = GL.•-cancelʳ {g = X15 • M2} {g' = M2 • X15} {h = p (s1 • s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00820.proved (MV00821.proved))) (trans (cong refl R085.proved) (move-product MV00821.proved (MV00820.proved))))

module r2b_ij153 where

  proved : X15 • M3 ≈ M3 • X15
  proved = GL.•-cancelʳ {g = X15 • M3} {g' = M3 • X15} {h = p (s2 • s1 • s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00822.proved (MV00823.proved))) (trans (cong refl R085.proved) (move-product MV00823.proved (MV00822.proved))))

module r2b_ij154 where

  proved : X15 • M4 ≈ M4 • X15
  proved = GL.•-cancelʳ {g = X15 • M4} {g' = M4 • X15} {h = p (s3 • s2 • s1 • s0 • s1 • s4 • s3 • s2)}
    (trans (sym (move-product MV00824.proved (MV00825.proved))) (trans (cong refl R085.proved) (move-product MV00825.proved (MV00824.proved))))
