{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B048 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00007 ; module MV00009 ; module MV00010 ; module MV00011 ; module MV00014 ; module MV00015 ; module MV00016 ; module MV00017 ; module MV00018 ; module MV00021 ; module MV00022 ; module MV00023 ; module MV00024 ; module MV00025 ; module MV00028 ; module MV00029 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00039 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053)

module MV01821 where

  proved : p (s0 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV01822 where

  proved : p (s1 • s0 • s1 • s2 • s3) • M0 ≈ M2 • p (s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV01823 where

  proved : p (s1 • s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01824 where

  proved : p (s1 • s0 • s2 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV01825 where

  proved : p (s1 • s0 • s2 • s3) • M4 ≈ M1 • p (s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV01826 where

  proved : p (s1 • s0 • s3) • M0 ≈ M2 • p (s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (MV00003.proved))) Eq.refl Eq.refl

module MV01827 where

  proved : p (s1 • s0 • s3) • M4 ≈ M3 • p (s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (MV00031.proved))) Eq.refl Eq.refl

module MV01828 where

  proved : p (s1 • s0) • M4 ≈ M4 • p (s1 • s0)
  proved = by-assoc-and (move-compose MV00029.proved (MV00028.proved)) Eq.refl Eq.refl

module MV01829 where

  proved : p (s1 • s0 • s4) • M0 ≈ M2 • p (s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (MV00004.proved))) Eq.refl Eq.refl

module MV01830 where

  proved : p (s1 • s0 • s4) • M4 ≈ M5 • p (s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00035.proved (MV00032.proved))) Eq.refl Eq.refl

module MV01831 where

  proved : p (s1 • s0 • s5 • s4) • M0 ≈ M2 • p (s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved)))) Eq.refl Eq.refl

module MV01832 where

  proved : p (s1 • s0 • s5 • s4) • M4 ≈ M6 • p (s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV01833 where

  proved : p (s1 • s0 • s6 • s5 • s4) • M0 ≈ M2 • p (s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved))))) Eq.refl Eq.refl

module MV01834 where

  proved : p (s1 • s0 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV01835 where

  proved : p (s2 • s1 • s0 • s1 • s2 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV01836 where

  proved : p (s2 • s1 • s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01837 where

  proved : p (s2 • s1 • s0 • s2 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV01838 where

  proved : p (s2 • s1 • s0 • s2 • s3) • M4 ≈ M1 • p (s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01839 where

  proved : p (s2 • s1 • s0 • s3) • M0 ≈ M3 • p (s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV01840 where

  proved : p (s2 • s1 • s0 • s3) • M4 ≈ M2 • p (s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV01841 where

  proved : p (s2 • s1 • s0) • M4 ≈ M4 • p (s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00030.proved (move-compose MV00029.proved (MV00028.proved))) Eq.refl Eq.refl

module MV01842 where

  proved : p (s2 • s1 • s0 • s4) • M0 ≈ M3 • p (s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00004.proved)))) Eq.refl Eq.refl

module MV01843 where

  proved : p (s2 • s1 • s0 • s4) • M4 ≈ M5 • p (s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV01844 where

  proved : p (s2 • s1 • s0 • s5 • s4) • M0 ≈ M3 • p (s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved))))) Eq.refl Eq.refl

module MV01845 where

  proved : p (s2 • s1 • s0 • s5 • s4) • M4 ≈ M6 • p (s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV01846 where

  proved : p (s2 • s1 • s0 • s6 • s5 • s4) • M0 ≈ M3 • p (s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved)))))) Eq.refl Eq.refl

module MV01847 where

  proved : p (s2 • s1 • s0 • s6 • s5 • s4) • M4 ≈ M7 • p (s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV01848 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s2 • s3) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV01849 where

  proved : p (s3 • s2 • s1 • s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01850 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s3) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV01851 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s3) • M4 ≈ M1 • p (s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01852 where

  proved : p (s3 • s2 • s1 • s0 • s3) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV01853 where

  proved : p (s3 • s2 • s1 • s0 • s3) • M4 ≈ M2 • p (s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01854 where

  proved : p (s3 • s2 • s1 • s0) • M4 ≈ M3 • p (s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (MV00028.proved)))) Eq.refl Eq.refl

module MV01855 where

  proved : p (s3 • s2 • s1 • s0 • s4) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00004.proved))))) Eq.refl Eq.refl

module MV01856 where

  proved : p (s3 • s2 • s1 • s0 • s4) • M4 ≈ M5 • p (s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV01857 where

  proved : p (s3 • s2 • s1 • s0 • s5 • s4) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved)))))) Eq.refl Eq.refl

module MV01858 where

  proved : p (s3 • s2 • s1 • s0 • s5 • s4) • M4 ≈ M6 • p (s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV01859 where

  proved : p (s3 • s2 • s1 • s0 • s6 • s5 • s4) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved))))))) Eq.refl Eq.refl

module MV01860 where

  proved : p (s3 • s2 • s1 • s0 • s6 • s5 • s4) • M4 ≈ M7 • p (s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV01861 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV01862 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01863 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s3) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV01864 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s3) • M4 ≈ M1 • p (s4 • s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01865 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV01866 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3) • M4 ≈ M2 • p (s4 • s3 • s2 • s1 • s0 • s3)
  proved = by-assoc-and (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01867 where

  proved : p (s4 • s3 • s2 • s1 • s0) • M4 ≈ M3 • p (s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (MV00028.proved))))) Eq.refl Eq.refl

module MV01868 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s4) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00004.proved)))))) Eq.refl Eq.refl

module MV01869 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s4) • M4 ≈ M4 • p (s4 • s3 • s2 • s1 • s0 • s4)
  proved = by-assoc-and (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV01870 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s5 • s4) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved))))))) Eq.refl Eq.refl

module MV01871 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s5 • s4) • M4 ≈ M6 • p (s4 • s3 • s2 • s1 • s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV01872 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved)))))))) Eq.refl Eq.refl

module MV01873 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4) • M4 ≈ M7 • p (s4 • s3 • s2 • s1 • s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV01874 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV01875 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s5 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved))))))))) Eq.refl Eq.refl

module MV01876 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved)))))))) Eq.refl Eq.refl
