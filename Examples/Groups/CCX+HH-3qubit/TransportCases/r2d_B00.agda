{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2d_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 as R095
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00003 ; module MV00004 ; module MV00028 ; module MV00031 ; module MV00032 ; module MV00630)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00635 ; module MV00636 ; module MV00637 ; module MV00638 ; module MV00639 ; module MV00640)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01801 ; module MV01802 ; module MV01803 ; module MV01804 ; module MV01805 ; module MV01806 ; module MV01807 ; module MV01808 ; module MV01809 ; module MV01810 ; module MV01811 ; module MV01812 ; module MV01813 ; module MV01814 ; module MV01815 ; module MV01816 ; module MV01817 ; module MV01818 ; module MV01819 ; module MV01820)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B048 using (module MV01821 ; module MV01822 ; module MV01823 ; module MV01824 ; module MV01825 ; module MV01826 ; module MV01827 ; module MV01828 ; module MV01829 ; module MV01830 ; module MV01831 ; module MV01832 ; module MV01833 ; module MV01834 ; module MV01835 ; module MV01836 ; module MV01837 ; module MV01838 ; module MV01839 ; module MV01840 ; module MV01841 ; module MV01842 ; module MV01843 ; module MV01844 ; module MV01845 ; module MV01846 ; module MV01847 ; module MV01848 ; module MV01849 ; module MV01850 ; module MV01851 ; module MV01852 ; module MV01853 ; module MV01854 ; module MV01855 ; module MV01856 ; module MV01857 ; module MV01858 ; module MV01859 ; module MV01860 ; module MV01861 ; module MV01862 ; module MV01863 ; module MV01864 ; module MV01865 ; module MV01866 ; module MV01867 ; module MV01868 ; module MV01869 ; module MV01870 ; module MV01871 ; module MV01872 ; module MV01873 ; module MV01874 ; module MV01875 ; module MV01876)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B049 using (module MV01877 ; module MV01878 ; module MV01879 ; module MV01880 ; module MV01881 ; module MV01882 ; module MV01883 ; module MV01884 ; module MV01885 ; module MV01886 ; module MV01887 ; module MV01888 ; module MV01889 ; module MV01890 ; module MV01891 ; module MV01892 ; module MV01893 ; module MV01894 ; module MV01895 ; module MV01896 ; module MV01897 ; module MV01898 ; module MV01899)

module r2d_ij01 where

  proved : M0 • M1 ≈ M1 • M0
  proved = GL.•-cancelʳ {g = M0 • M1} {g' = M1 • M0} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV01801.proved (MV01802.proved))) (trans (cong refl R095.proved) (move-product MV01802.proved (MV01801.proved))))

module r2d_ij02 where

  proved : M0 • M2 ≈ M2 • M0
  proved = GL.•-cancelʳ {g = M0 • M2} {g' = M2 • M0} {h = p (s2 • s3)}
    (trans (sym (move-product MV01803.proved (MV01804.proved))) (trans (cong refl R095.proved) (move-product MV01804.proved (MV01803.proved))))

module r2d_ij03 where

  proved : M0 • M3 ≈ M3 • M0
  proved = GL.•-cancelʳ {g = M0 • M3} {g' = M3 • M0} {h = p (s3)}
    (trans (sym (move-product MV00003.proved (MV00031.proved))) (trans (cong refl R095.proved) (move-product MV00031.proved (MV00003.proved))))

module r2d_ij04 where

  proved : M0 • M4 ≈ M4 • M0
  proved = GL.•-cancelʳ {g = M0 • M4} {g' = M4 • M0} {h = p (ε)}
    (trans (sym (move-product MV00635.proved (MV01805.proved))) (trans (cong refl R095.proved) (move-product MV01805.proved (MV00635.proved))))

module r2d_ij05 where

  proved : M0 • M5 ≈ M5 • M0
  proved = GL.•-cancelʳ {g = M0 • M5} {g' = M5 • M0} {h = p (s4)}
    (trans (sym (move-product MV00004.proved (MV00032.proved))) (trans (cong refl R095.proved) (move-product MV00032.proved (MV00004.proved))))

module r2d_ij06 where

  proved : M0 • M6 ≈ M6 • M0
  proved = GL.•-cancelʳ {g = M0 • M6} {g' = M6 • M0} {h = p (s5 • s4)}
    (trans (sym (move-product MV01806.proved (MV01807.proved))) (trans (cong refl R095.proved) (move-product MV01807.proved (MV01806.proved))))

module r2d_ij07 where

  proved : M0 • M7 ≈ M7 • M0
  proved = GL.•-cancelʳ {g = M0 • M7} {g' = M7 • M0} {h = p (s6 • s5 • s4)}
    (trans (sym (move-product MV01808.proved (MV01809.proved))) (trans (cong refl R095.proved) (move-product MV01809.proved (MV01808.proved))))

module r2d_ij10 where

  proved : M1 • M0 ≈ M0 • M1
  proved = GL.•-cancelʳ {g = M1 • M0} {g' = M0 • M1} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01810.proved (MV01811.proved))) (trans (cong refl R095.proved) (move-product MV01811.proved (MV01810.proved))))

module r2d_ij12 where

  proved : M1 • M2 ≈ M2 • M1
  proved = GL.•-cancelʳ {g = M1 • M2} {g' = M2 • M1} {h = p (s0 • s2 • s3)}
    (trans (sym (move-product MV01812.proved (MV01813.proved))) (trans (cong refl R095.proved) (move-product MV01813.proved (MV01812.proved))))

module r2d_ij13 where

  proved : M1 • M3 ≈ M3 • M1
  proved = GL.•-cancelʳ {g = M1 • M3} {g' = M3 • M1} {h = p (s0 • s3)}
    (trans (sym (move-product MV01814.proved (MV01815.proved))) (trans (cong refl R095.proved) (move-product MV01815.proved (MV01814.proved))))

module r2d_ij14 where

  proved : M1 • M4 ≈ M4 • M1
  proved = GL.•-cancelʳ {g = M1 • M4} {g' = M4 • M1} {h = p (s0)}
    (trans (sym (move-product MV00000.proved (MV00028.proved))) (trans (cong refl R095.proved) (move-product MV00028.proved (MV00000.proved))))

module r2d_ij15 where

  proved : M1 • M5 ≈ M5 • M1
  proved = GL.•-cancelʳ {g = M1 • M5} {g' = M5 • M1} {h = p (s0 • s4)}
    (trans (sym (move-product MV01816.proved (MV01817.proved))) (trans (cong refl R095.proved) (move-product MV01817.proved (MV01816.proved))))

module r2d_ij16 where

  proved : M1 • M6 ≈ M6 • M1
  proved = GL.•-cancelʳ {g = M1 • M6} {g' = M6 • M1} {h = p (s0 • s5 • s4)}
    (trans (sym (move-product MV01818.proved (MV01819.proved))) (trans (cong refl R095.proved) (move-product MV01819.proved (MV01818.proved))))

module r2d_ij17 where

  proved : M1 • M7 ≈ M7 • M1
  proved = GL.•-cancelʳ {g = M1 • M7} {g' = M7 • M1} {h = p (s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01820.proved (MV01821.proved))) (trans (cong refl R095.proved) (move-product MV01821.proved (MV01820.proved))))

module r2d_ij20 where

  proved : M2 • M0 ≈ M0 • M2
  proved = GL.•-cancelʳ {g = M2 • M0} {g' = M0 • M2} {h = p (s1 • s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01822.proved (MV01823.proved))) (trans (cong refl R095.proved) (move-product MV01823.proved (MV01822.proved))))

module r2d_ij21 where

  proved : M2 • M1 ≈ M1 • M2
  proved = GL.•-cancelʳ {g = M2 • M1} {g' = M1 • M2} {h = p (s1 • s0 • s2 • s3)}
    (trans (sym (move-product MV01824.proved (MV01825.proved))) (trans (cong refl R095.proved) (move-product MV01825.proved (MV01824.proved))))

module r2d_ij23 where

  proved : M2 • M3 ≈ M3 • M2
  proved = GL.•-cancelʳ {g = M2 • M3} {g' = M3 • M2} {h = p (s1 • s0 • s3)}
    (trans (sym (move-product MV01826.proved (MV01827.proved))) (trans (cong refl R095.proved) (move-product MV01827.proved (MV01826.proved))))

module r2d_ij24 where

  proved : M2 • M4 ≈ M4 • M2
  proved = GL.•-cancelʳ {g = M2 • M4} {g' = M4 • M2} {h = p (s1 • s0)}
    (trans (sym (move-product MV00636.proved (MV01828.proved))) (trans (cong refl R095.proved) (move-product MV01828.proved (MV00636.proved))))

module r2d_ij25 where

  proved : M2 • M5 ≈ M5 • M2
  proved = GL.•-cancelʳ {g = M2 • M5} {g' = M5 • M2} {h = p (s1 • s0 • s4)}
    (trans (sym (move-product MV01829.proved (MV01830.proved))) (trans (cong refl R095.proved) (move-product MV01830.proved (MV01829.proved))))

module r2d_ij26 where

  proved : M2 • M6 ≈ M6 • M2
  proved = GL.•-cancelʳ {g = M2 • M6} {g' = M6 • M2} {h = p (s1 • s0 • s5 • s4)}
    (trans (sym (move-product MV01831.proved (MV01832.proved))) (trans (cong refl R095.proved) (move-product MV01832.proved (MV01831.proved))))

module r2d_ij27 where

  proved : M2 • M7 ≈ M7 • M2
  proved = GL.•-cancelʳ {g = M2 • M7} {g' = M7 • M2} {h = p (s1 • s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01833.proved (MV01834.proved))) (trans (cong refl R095.proved) (move-product MV01834.proved (MV01833.proved))))

module r2d_ij30 where

  proved : M3 • M0 ≈ M0 • M3
  proved = GL.•-cancelʳ {g = M3 • M0} {g' = M0 • M3} {h = p (s2 • s1 • s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01835.proved (MV01836.proved))) (trans (cong refl R095.proved) (move-product MV01836.proved (MV01835.proved))))

module r2d_ij31 where

  proved : M3 • M1 ≈ M1 • M3
  proved = GL.•-cancelʳ {g = M3 • M1} {g' = M1 • M3} {h = p (s2 • s1 • s0 • s2 • s3)}
    (trans (sym (move-product MV01837.proved (MV01838.proved))) (trans (cong refl R095.proved) (move-product MV01838.proved (MV01837.proved))))

module r2d_ij32 where

  proved : M3 • M2 ≈ M2 • M3
  proved = GL.•-cancelʳ {g = M3 • M2} {g' = M2 • M3} {h = p (s2 • s1 • s0 • s3)}
    (trans (sym (move-product MV01839.proved (MV01840.proved))) (trans (cong refl R095.proved) (move-product MV01840.proved (MV01839.proved))))

module r2d_ij34 where

  proved : M3 • M4 ≈ M4 • M3
  proved = GL.•-cancelʳ {g = M3 • M4} {g' = M4 • M3} {h = p (s2 • s1 • s0)}
    (trans (sym (move-product MV00630.proved (MV01841.proved))) (trans (cong refl R095.proved) (move-product MV01841.proved (MV00630.proved))))

module r2d_ij35 where

  proved : M3 • M5 ≈ M5 • M3
  proved = GL.•-cancelʳ {g = M3 • M5} {g' = M5 • M3} {h = p (s2 • s1 • s0 • s4)}
    (trans (sym (move-product MV01842.proved (MV01843.proved))) (trans (cong refl R095.proved) (move-product MV01843.proved (MV01842.proved))))

module r2d_ij36 where

  proved : M3 • M6 ≈ M6 • M3
  proved = GL.•-cancelʳ {g = M3 • M6} {g' = M6 • M3} {h = p (s2 • s1 • s0 • s5 • s4)}
    (trans (sym (move-product MV01844.proved (MV01845.proved))) (trans (cong refl R095.proved) (move-product MV01845.proved (MV01844.proved))))

module r2d_ij37 where

  proved : M3 • M7 ≈ M7 • M3
  proved = GL.•-cancelʳ {g = M3 • M7} {g' = M7 • M3} {h = p (s2 • s1 • s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01846.proved (MV01847.proved))) (trans (cong refl R095.proved) (move-product MV01847.proved (MV01846.proved))))

module r2d_ij40 where

  proved : M4 • M0 ≈ M0 • M4
  proved = GL.•-cancelʳ {g = M4 • M0} {g' = M0 • M4} {h = p (s3 • s2 • s1 • s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01848.proved (MV01849.proved))) (trans (cong refl R095.proved) (move-product MV01849.proved (MV01848.proved))))

module r2d_ij41 where

  proved : M4 • M1 ≈ M1 • M4
  proved = GL.•-cancelʳ {g = M4 • M1} {g' = M1 • M4} {h = p (s3 • s2 • s1 • s0 • s2 • s3)}
    (trans (sym (move-product MV01850.proved (MV01851.proved))) (trans (cong refl R095.proved) (move-product MV01851.proved (MV01850.proved))))

module r2d_ij42 where

  proved : M4 • M2 ≈ M2 • M4
  proved = GL.•-cancelʳ {g = M4 • M2} {g' = M2 • M4} {h = p (s3 • s2 • s1 • s0 • s3)}
    (trans (sym (move-product MV01852.proved (MV01853.proved))) (trans (cong refl R095.proved) (move-product MV01853.proved (MV01852.proved))))

module r2d_ij43 where

  proved : M4 • M3 ≈ M3 • M4
  proved = GL.•-cancelʳ {g = M4 • M3} {g' = M3 • M4} {h = p (s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00637.proved (MV01854.proved))) (trans (cong refl R095.proved) (move-product MV01854.proved (MV00637.proved))))

module r2d_ij45 where

  proved : M4 • M5 ≈ M5 • M4
  proved = GL.•-cancelʳ {g = M4 • M5} {g' = M5 • M4} {h = p (s3 • s2 • s1 • s0 • s4)}
    (trans (sym (move-product MV01855.proved (MV01856.proved))) (trans (cong refl R095.proved) (move-product MV01856.proved (MV01855.proved))))

module r2d_ij46 where

  proved : M4 • M6 ≈ M6 • M4
  proved = GL.•-cancelʳ {g = M4 • M6} {g' = M6 • M4} {h = p (s3 • s2 • s1 • s0 • s5 • s4)}
    (trans (sym (move-product MV01857.proved (MV01858.proved))) (trans (cong refl R095.proved) (move-product MV01858.proved (MV01857.proved))))

module r2d_ij47 where

  proved : M4 • M7 ≈ M7 • M4
  proved = GL.•-cancelʳ {g = M4 • M7} {g' = M7 • M4} {h = p (s3 • s2 • s1 • s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01859.proved (MV01860.proved))) (trans (cong refl R095.proved) (move-product MV01860.proved (MV01859.proved))))

module r2d_ij50 where

  proved : M5 • M0 ≈ M0 • M5
  proved = GL.•-cancelʳ {g = M5 • M0} {g' = M0 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01861.proved (MV01862.proved))) (trans (cong refl R095.proved) (move-product MV01862.proved (MV01861.proved))))

module r2d_ij51 where

  proved : M5 • M1 ≈ M1 • M5
  proved = GL.•-cancelʳ {g = M5 • M1} {g' = M1 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s2 • s3)}
    (trans (sym (move-product MV01863.proved (MV01864.proved))) (trans (cong refl R095.proved) (move-product MV01864.proved (MV01863.proved))))

module r2d_ij52 where

  proved : M5 • M2 ≈ M2 • M5
  proved = GL.•-cancelʳ {g = M5 • M2} {g' = M2 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s3)}
    (trans (sym (move-product MV01865.proved (MV01866.proved))) (trans (cong refl R095.proved) (move-product MV01866.proved (MV01865.proved))))

module r2d_ij53 where

  proved : M5 • M3 ≈ M3 • M5
  proved = GL.•-cancelʳ {g = M5 • M3} {g' = M3 • M5} {h = p (s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00638.proved (MV01867.proved))) (trans (cong refl R095.proved) (move-product MV01867.proved (MV00638.proved))))

module r2d_ij54 where

  proved : M5 • M4 ≈ M4 • M5
  proved = GL.•-cancelʳ {g = M5 • M4} {g' = M4 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s4)}
    (trans (sym (move-product MV01868.proved (MV01869.proved))) (trans (cong refl R095.proved) (move-product MV01869.proved (MV01868.proved))))

module r2d_ij56 where

  proved : M5 • M6 ≈ M6 • M5
  proved = GL.•-cancelʳ {g = M5 • M6} {g' = M6 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s5 • s4)}
    (trans (sym (move-product MV01870.proved (MV01871.proved))) (trans (cong refl R095.proved) (move-product MV01871.proved (MV01870.proved))))

module r2d_ij57 where

  proved : M5 • M7 ≈ M7 • M5
  proved = GL.•-cancelʳ {g = M5 • M7} {g' = M7 • M5} {h = p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01872.proved (MV01873.proved))) (trans (cong refl R095.proved) (move-product MV01873.proved (MV01872.proved))))

module r2d_ij60 where

  proved : M6 • M0 ≈ M0 • M6
  proved = GL.•-cancelʳ {g = M6 • M0} {g' = M0 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01874.proved (MV01875.proved))) (trans (cong refl R095.proved) (move-product MV01875.proved (MV01874.proved))))

module r2d_ij61 where

  proved : M6 • M1 ≈ M1 • M6
  proved = GL.•-cancelʳ {g = M6 • M1} {g' = M1 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)}
    (trans (sym (move-product MV01876.proved (MV01877.proved))) (trans (cong refl R095.proved) (move-product MV01877.proved (MV01876.proved))))

module r2d_ij62 where

  proved : M6 • M2 ≈ M2 • M6
  proved = GL.•-cancelʳ {g = M6 • M2} {g' = M2 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s3)}
    (trans (sym (move-product MV01878.proved (MV01879.proved))) (trans (cong refl R095.proved) (move-product MV01879.proved (MV01878.proved))))

module r2d_ij63 where

  proved : M6 • M3 ≈ M3 • M6
  proved = GL.•-cancelʳ {g = M6 • M3} {g' = M3 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00639.proved (MV01880.proved))) (trans (cong refl R095.proved) (move-product MV01880.proved (MV00639.proved))))

module r2d_ij64 where

  proved : M6 • M4 ≈ M4 • M6
  proved = GL.•-cancelʳ {g = M6 • M4} {g' = M4 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s4)}
    (trans (sym (move-product MV01881.proved (MV01882.proved))) (trans (cong refl R095.proved) (move-product MV01882.proved (MV01881.proved))))

module r2d_ij65 where

  proved : M6 • M5 ≈ M5 • M6
  proved = GL.•-cancelʳ {g = M6 • M5} {g' = M5 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)}
    (trans (sym (move-product MV01883.proved (MV01884.proved))) (trans (cong refl R095.proved) (move-product MV01884.proved (MV01883.proved))))

module r2d_ij67 where

  proved : M6 • M7 ≈ M7 • M6
  proved = GL.•-cancelʳ {g = M6 • M7} {g' = M7 • M6} {h = p (s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01885.proved (MV01886.proved))) (trans (cong refl R095.proved) (move-product MV01886.proved (MV01885.proved))))

module r2d_ij70 where

  proved : M7 • M0 ≈ M0 • M7
  proved = GL.•-cancelʳ {g = M7 • M0} {g' = M0 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01887.proved (MV01888.proved))) (trans (cong refl R095.proved) (move-product MV01888.proved (MV01887.proved))))

module r2d_ij71 where

  proved : M7 • M1 ≈ M1 • M7
  proved = GL.•-cancelʳ {g = M7 • M1} {g' = M1 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)}
    (trans (sym (move-product MV01889.proved (MV01890.proved))) (trans (cong refl R095.proved) (move-product MV01890.proved (MV01889.proved))))

module r2d_ij72 where

  proved : M7 • M2 ≈ M2 • M7
  proved = GL.•-cancelʳ {g = M7 • M2} {g' = M2 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3)}
    (trans (sym (move-product MV01891.proved (MV01892.proved))) (trans (cong refl R095.proved) (move-product MV01892.proved (MV01891.proved))))

module r2d_ij73 where

  proved : M7 • M3 ≈ M3 • M7
  proved = GL.•-cancelʳ {g = M7 • M3} {g' = M3 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0)}
    (trans (sym (move-product MV00640.proved (MV01893.proved))) (trans (cong refl R095.proved) (move-product MV01893.proved (MV00640.proved))))

module r2d_ij74 where

  proved : M7 • M4 ≈ M4 • M7
  proved = GL.•-cancelʳ {g = M7 • M4} {g' = M4 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4)}
    (trans (sym (move-product MV01894.proved (MV01895.proved))) (trans (cong refl R095.proved) (move-product MV01895.proved (MV01894.proved))))

module r2d_ij75 where

  proved : M7 • M5 ≈ M5 • M7
  proved = GL.•-cancelʳ {g = M7 • M5} {g' = M5 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s5 • s4)}
    (trans (sym (move-product MV01896.proved (MV01897.proved))) (trans (cong refl R095.proved) (move-product MV01897.proved (MV01896.proved))))

module r2d_ij76 where

  proved : M7 • M6 ≈ M6 • M7
  proved = GL.•-cancelʳ {g = M7 • M6} {g' = M6 • M7} {h = p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)}
    (trans (sym (move-product MV01898.proved (MV01899.proved))) (trans (cong refl R095.proved) (move-product MV01899.proved (MV01898.proved))))
