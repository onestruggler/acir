{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M0 ; M1 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as R094
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00659 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675 ; module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684 ; module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689 ; module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696 ; module MV00697 ; module MV00698 ; module MV00699 ; module MV00700 ; module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01802 ; module MV01811)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B049 using (module MV01900 ; module MV01901 ; module MV01902 ; module MV01903 ; module MV01904 ; module MV01905 ; module MV01906 ; module MV01907 ; module MV01908 ; module MV01909 ; module MV01910 ; module MV01911 ; module MV01912 ; module MV01913 ; module MV01914 ; module MV01915 ; module MV01916 ; module MV01917 ; module MV01918)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B050 using (module MV01919 ; module MV01920 ; module MV01921 ; module MV01922 ; module MV01923 ; module MV01924 ; module MV01925 ; module MV01926 ; module MV01927 ; module MV01928 ; module MV01929 ; module MV01930 ; module MV01931 ; module MV01932 ; module MV01933 ; module MV01934 ; module MV01935 ; module MV01936 ; module MV01937 ; module MV01938 ; module MV01939 ; module MV01940 ; module MV01941 ; module MV01942 ; module MV01943 ; module MV01944 ; module MV01945 ; module MV01946 ; module MV01947 ; module MV01948 ; module MV01949 ; module MV01950 ; module MV01951 ; module MV01952 ; module MV01953 ; module MV01954 ; module MV01955 ; module MV01956)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B051 using (module MV01957 ; module MV01958 ; module MV01959 ; module MV01960 ; module MV01961 ; module MV01962 ; module MV01963 ; module MV01964 ; module MV01965 ; module MV01966)

module r2e_ij01234 where

  proved : M0 • K1234 ≈ K1234 • M0
  proved = GL.•-cancelʳ {g = M0 • K1234} {g' = K1234 • M0} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV01811.proved (MV00675.proved))) (trans (cong refl R094.proved) (move-product MV00675.proved (MV01811.proved))))

module r2e_ij01235 where

  proved : M0 • K1235 ≈ K1235 • M0
  proved = GL.•-cancelʳ {g = M0 • K1235} {g' = K1235 • M0} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV01900.proved (MV00676.proved))) (trans (cong refl R094.proved) (move-product MV00676.proved (MV01900.proved))))

module r2e_ij01236 where

  proved : M0 • K1236 ≈ K1236 • M0
  proved = GL.•-cancelʳ {g = M0 • K1236} {g' = K1236 • M0} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01901.proved (MV00677.proved))) (trans (cong refl R094.proved) (move-product MV00677.proved (MV01901.proved))))

module r2e_ij01237 where

  proved : M0 • K1237 ≈ K1237 • M0
  proved = GL.•-cancelʳ {g = M0 • K1237} {g' = K1237 • M0} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01902.proved (MV00678.proved))) (trans (cong refl R094.proved) (move-product MV00678.proved (MV01902.proved))))

module r2e_ij01245 where

  proved : M0 • K1245 ≈ K1245 • M0
  proved = GL.•-cancelʳ {g = M0 • K1245} {g' = K1245 • M0} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01903.proved (MV00679.proved))) (trans (cong refl R094.proved) (move-product MV00679.proved (MV01903.proved))))

module r2e_ij01246 where

  proved : M0 • K1246 ≈ K1246 • M0
  proved = GL.•-cancelʳ {g = M0 • K1246} {g' = K1246 • M0} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01904.proved (MV00680.proved))) (trans (cong refl R094.proved) (move-product MV00680.proved (MV01904.proved))))

module r2e_ij01247 where

  proved : M0 • K1247 ≈ K1247 • M0
  proved = GL.•-cancelʳ {g = M0 • K1247} {g' = K1247 • M0} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01905.proved (MV00681.proved))) (trans (cong refl R094.proved) (move-product MV00681.proved (MV01905.proved))))

module r2e_ij01256 where

  proved : M0 • K1256 ≈ K1256 • M0
  proved = GL.•-cancelʳ {g = M0 • K1256} {g' = K1256 • M0} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01906.proved (MV00682.proved))) (trans (cong refl R094.proved) (move-product MV00682.proved (MV01906.proved))))

module r2e_ij01257 where

  proved : M0 • K1257 ≈ K1257 • M0
  proved = GL.•-cancelʳ {g = M0 • K1257} {g' = K1257 • M0} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01907.proved (MV00683.proved))) (trans (cong refl R094.proved) (move-product MV00683.proved (MV01907.proved))))

module r2e_ij01267 where

  proved : M0 • K1267 ≈ K1267 • M0
  proved = GL.•-cancelʳ {g = M0 • K1267} {g' = K1267 • M0} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01908.proved (MV00684.proved))) (trans (cong refl R094.proved) (move-product MV00684.proved (MV01908.proved))))

module r2e_ij01345 where

  proved : M0 • K1345 ≈ K1345 • M0
  proved = GL.•-cancelʳ {g = M0 • K1345} {g' = K1345 • M0} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01909.proved (MV00685.proved))) (trans (cong refl R094.proved) (move-product MV00685.proved (MV01909.proved))))

module r2e_ij01346 where

  proved : M0 • K1346 ≈ K1346 • M0
  proved = GL.•-cancelʳ {g = M0 • K1346} {g' = K1346 • M0} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01910.proved (MV00686.proved))) (trans (cong refl R094.proved) (move-product MV00686.proved (MV01910.proved))))

module r2e_ij01347 where

  proved : M0 • K1347 ≈ K1347 • M0
  proved = GL.•-cancelʳ {g = M0 • K1347} {g' = K1347 • M0} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01911.proved (MV00687.proved))) (trans (cong refl R094.proved) (move-product MV00687.proved (MV01911.proved))))

module r2e_ij01356 where

  proved : M0 • K1356 ≈ K1356 • M0
  proved = GL.•-cancelʳ {g = M0 • K1356} {g' = K1356 • M0} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01912.proved (MV00688.proved))) (trans (cong refl R094.proved) (move-product MV00688.proved (MV01912.proved))))

module r2e_ij01357 where

  proved : M0 • K1357 ≈ K1357 • M0
  proved = GL.•-cancelʳ {g = M0 • K1357} {g' = K1357 • M0} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01913.proved (MV00689.proved))) (trans (cong refl R094.proved) (move-product MV00689.proved (MV01913.proved))))

module r2e_ij01367 where

  proved : M0 • K1367 ≈ K1367 • M0
  proved = GL.•-cancelʳ {g = M0 • K1367} {g' = K1367 • M0} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01914.proved (MV00690.proved))) (trans (cong refl R094.proved) (move-product MV00690.proved (MV01914.proved))))

module r2e_ij01456 where

  proved : M0 • K1456 ≈ K1456 • M0
  proved = GL.•-cancelʳ {g = M0 • K1456} {g' = K1456 • M0} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01915.proved (MV00691.proved))) (trans (cong refl R094.proved) (move-product MV00691.proved (MV01915.proved))))

module r2e_ij01457 where

  proved : M0 • K1457 ≈ K1457 • M0
  proved = GL.•-cancelʳ {g = M0 • K1457} {g' = K1457 • M0} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01916.proved (MV00692.proved))) (trans (cong refl R094.proved) (move-product MV00692.proved (MV01916.proved))))

module r2e_ij01467 where

  proved : M0 • K1467 ≈ K1467 • M0
  proved = GL.•-cancelʳ {g = M0 • K1467} {g' = K1467 • M0} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01917.proved (MV00693.proved))) (trans (cong refl R094.proved) (move-product MV00693.proved (MV01917.proved))))

module r2e_ij01567 where

  proved : M0 • K1567 ≈ K1567 • M0
  proved = GL.•-cancelʳ {g = M0 • K1567} {g' = K1567 • M0} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01918.proved (MV00694.proved))) (trans (cong refl R094.proved) (move-product MV00694.proved (MV01918.proved))))

module r2e_ij02345 where

  proved : M0 • K2345 ≈ K2345 • M0
  proved = GL.•-cancelʳ {g = M0 • K2345} {g' = K2345 • M0} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01919.proved (MV00695.proved))) (trans (cong refl R094.proved) (move-product MV00695.proved (MV01919.proved))))

module r2e_ij02346 where

  proved : M0 • K2346 ≈ K2346 • M0
  proved = GL.•-cancelʳ {g = M0 • K2346} {g' = K2346 • M0} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01920.proved (MV00696.proved))) (trans (cong refl R094.proved) (move-product MV00696.proved (MV01920.proved))))

module r2e_ij02347 where

  proved : M0 • K2347 ≈ K2347 • M0
  proved = GL.•-cancelʳ {g = M0 • K2347} {g' = K2347 • M0} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01921.proved (MV00697.proved))) (trans (cong refl R094.proved) (move-product MV00697.proved (MV01921.proved))))

module r2e_ij02356 where

  proved : M0 • K2356 ≈ K2356 • M0
  proved = GL.•-cancelʳ {g = M0 • K2356} {g' = K2356 • M0} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01922.proved (MV00698.proved))) (trans (cong refl R094.proved) (move-product MV00698.proved (MV01922.proved))))

module r2e_ij02357 where

  proved : M0 • K2357 ≈ K2357 • M0
  proved = GL.•-cancelʳ {g = M0 • K2357} {g' = K2357 • M0} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01923.proved (MV00699.proved))) (trans (cong refl R094.proved) (move-product MV00699.proved (MV01923.proved))))

module r2e_ij02367 where

  proved : M0 • K2367 ≈ K2367 • M0
  proved = GL.•-cancelʳ {g = M0 • K2367} {g' = K2367 • M0} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01924.proved (MV00700.proved))) (trans (cong refl R094.proved) (move-product MV00700.proved (MV01924.proved))))

module r2e_ij02456 where

  proved : M0 • K2456 ≈ K2456 • M0
  proved = GL.•-cancelʳ {g = M0 • K2456} {g' = K2456 • M0} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01925.proved (MV00701.proved))) (trans (cong refl R094.proved) (move-product MV00701.proved (MV01925.proved))))

module r2e_ij02457 where

  proved : M0 • K2457 ≈ K2457 • M0
  proved = GL.•-cancelʳ {g = M0 • K2457} {g' = K2457 • M0} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01926.proved (MV00702.proved))) (trans (cong refl R094.proved) (move-product MV00702.proved (MV01926.proved))))

module r2e_ij02467 where

  proved : M0 • K2467 ≈ K2467 • M0
  proved = GL.•-cancelʳ {g = M0 • K2467} {g' = K2467 • M0} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01927.proved (MV00703.proved))) (trans (cong refl R094.proved) (move-product MV00703.proved (MV01927.proved))))

module r2e_ij02567 where

  proved : M0 • K2567 ≈ K2567 • M0
  proved = GL.•-cancelʳ {g = M0 • K2567} {g' = K2567 • M0} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01928.proved (MV00704.proved))) (trans (cong refl R094.proved) (move-product MV00704.proved (MV01928.proved))))

module r2e_ij03456 where

  proved : M0 • K3456 ≈ K3456 • M0
  proved = GL.•-cancelʳ {g = M0 • K3456} {g' = K3456 • M0} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01929.proved (MV00705.proved))) (trans (cong refl R094.proved) (move-product MV00705.proved (MV01929.proved))))

module r2e_ij03457 where

  proved : M0 • K3457 ≈ K3457 • M0
  proved = GL.•-cancelʳ {g = M0 • K3457} {g' = K3457 • M0} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01930.proved (MV00706.proved))) (trans (cong refl R094.proved) (move-product MV00706.proved (MV01930.proved))))

module r2e_ij03467 where

  proved : M0 • K3467 ≈ K3467 • M0
  proved = GL.•-cancelʳ {g = M0 • K3467} {g' = K3467 • M0} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01931.proved (MV00707.proved))) (trans (cong refl R094.proved) (move-product MV00707.proved (MV01931.proved))))

module r2e_ij03567 where

  proved : M0 • K3567 ≈ K3567 • M0
  proved = GL.•-cancelʳ {g = M0 • K3567} {g' = K3567 • M0} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01932.proved (MV00708.proved))) (trans (cong refl R094.proved) (move-product MV00708.proved (MV01932.proved))))

module r2e_ij04567 where

  proved : M0 • K4567 ≈ K4567 • M0
  proved = GL.•-cancelʳ {g = M0 • K4567} {g' = K4567 • M0} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01933.proved (MV00632.proved))) (trans (cong refl R094.proved) (move-product MV00632.proved (MV01933.proved))))

module r2e_ij10234 where

  proved : M1 • K0234 ≈ K0234 • M1
  proved = GL.•-cancelʳ {g = M1 • K0234} {g' = K0234 • M1} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV01802.proved (MV00655.proved))) (trans (cong refl R094.proved) (move-product MV00655.proved (MV01802.proved))))

module r2e_ij10235 where

  proved : M1 • K0235 ≈ K0235 • M1
  proved = GL.•-cancelʳ {g = M1 • K0235} {g' = K0235 • M1} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV01934.proved (MV00656.proved))) (trans (cong refl R094.proved) (move-product MV00656.proved (MV01934.proved))))

module r2e_ij10236 where

  proved : M1 • K0236 ≈ K0236 • M1
  proved = GL.•-cancelʳ {g = M1 • K0236} {g' = K0236 • M1} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01935.proved (MV00657.proved))) (trans (cong refl R094.proved) (move-product MV00657.proved (MV01935.proved))))

module r2e_ij10237 where

  proved : M1 • K0237 ≈ K0237 • M1
  proved = GL.•-cancelʳ {g = M1 • K0237} {g' = K0237 • M1} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01936.proved (MV00658.proved))) (trans (cong refl R094.proved) (move-product MV00658.proved (MV01936.proved))))

module r2e_ij10245 where

  proved : M1 • K0245 ≈ K0245 • M1
  proved = GL.•-cancelʳ {g = M1 • K0245} {g' = K0245 • M1} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01937.proved (MV00659.proved))) (trans (cong refl R094.proved) (move-product MV00659.proved (MV01937.proved))))

module r2e_ij10246 where

  proved : M1 • K0246 ≈ K0246 • M1
  proved = GL.•-cancelʳ {g = M1 • K0246} {g' = K0246 • M1} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01938.proved (MV00660.proved))) (trans (cong refl R094.proved) (move-product MV00660.proved (MV01938.proved))))

module r2e_ij10247 where

  proved : M1 • K0247 ≈ K0247 • M1
  proved = GL.•-cancelʳ {g = M1 • K0247} {g' = K0247 • M1} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01939.proved (MV00661.proved))) (trans (cong refl R094.proved) (move-product MV00661.proved (MV01939.proved))))

module r2e_ij10256 where

  proved : M1 • K0256 ≈ K0256 • M1
  proved = GL.•-cancelʳ {g = M1 • K0256} {g' = K0256 • M1} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01940.proved (MV00662.proved))) (trans (cong refl R094.proved) (move-product MV00662.proved (MV01940.proved))))

module r2e_ij10257 where

  proved : M1 • K0257 ≈ K0257 • M1
  proved = GL.•-cancelʳ {g = M1 • K0257} {g' = K0257 • M1} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01941.proved (MV00663.proved))) (trans (cong refl R094.proved) (move-product MV00663.proved (MV01941.proved))))

module r2e_ij10267 where

  proved : M1 • K0267 ≈ K0267 • M1
  proved = GL.•-cancelʳ {g = M1 • K0267} {g' = K0267 • M1} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01942.proved (MV00664.proved))) (trans (cong refl R094.proved) (move-product MV00664.proved (MV01942.proved))))

module r2e_ij10345 where

  proved : M1 • K0345 ≈ K0345 • M1
  proved = GL.•-cancelʳ {g = M1 • K0345} {g' = K0345 • M1} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01943.proved (MV00665.proved))) (trans (cong refl R094.proved) (move-product MV00665.proved (MV01943.proved))))

module r2e_ij10346 where

  proved : M1 • K0346 ≈ K0346 • M1
  proved = GL.•-cancelʳ {g = M1 • K0346} {g' = K0346 • M1} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01944.proved (MV00666.proved))) (trans (cong refl R094.proved) (move-product MV00666.proved (MV01944.proved))))

module r2e_ij10347 where

  proved : M1 • K0347 ≈ K0347 • M1
  proved = GL.•-cancelʳ {g = M1 • K0347} {g' = K0347 • M1} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01945.proved (MV00667.proved))) (trans (cong refl R094.proved) (move-product MV00667.proved (MV01945.proved))))

module r2e_ij10356 where

  proved : M1 • K0356 ≈ K0356 • M1
  proved = GL.•-cancelʳ {g = M1 • K0356} {g' = K0356 • M1} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01946.proved (MV00668.proved))) (trans (cong refl R094.proved) (move-product MV00668.proved (MV01946.proved))))

module r2e_ij10357 where

  proved : M1 • K0357 ≈ K0357 • M1
  proved = GL.•-cancelʳ {g = M1 • K0357} {g' = K0357 • M1} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01947.proved (MV00669.proved))) (trans (cong refl R094.proved) (move-product MV00669.proved (MV01947.proved))))

module r2e_ij10367 where

  proved : M1 • K0367 ≈ K0367 • M1
  proved = GL.•-cancelʳ {g = M1 • K0367} {g' = K0367 • M1} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01948.proved (MV00670.proved))) (trans (cong refl R094.proved) (move-product MV00670.proved (MV01948.proved))))

module r2e_ij10456 where

  proved : M1 • K0456 ≈ K0456 • M1
  proved = GL.•-cancelʳ {g = M1 • K0456} {g' = K0456 • M1} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01949.proved (MV00671.proved))) (trans (cong refl R094.proved) (move-product MV00671.proved (MV01949.proved))))

module r2e_ij10457 where

  proved : M1 • K0457 ≈ K0457 • M1
  proved = GL.•-cancelʳ {g = M1 • K0457} {g' = K0457 • M1} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01950.proved (MV00672.proved))) (trans (cong refl R094.proved) (move-product MV00672.proved (MV01950.proved))))

module r2e_ij10467 where

  proved : M1 • K0467 ≈ K0467 • M1
  proved = GL.•-cancelʳ {g = M1 • K0467} {g' = K0467 • M1} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01951.proved (MV00673.proved))) (trans (cong refl R094.proved) (move-product MV00673.proved (MV01951.proved))))

module r2e_ij10567 where

  proved : M1 • K0567 ≈ K0567 • M1
  proved = GL.•-cancelʳ {g = M1 • K0567} {g' = K0567 • M1} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01952.proved (MV00674.proved))) (trans (cong refl R094.proved) (move-product MV00674.proved (MV01952.proved))))

module r2e_ij12345 where

  proved : M1 • K2345 ≈ K2345 • M1
  proved = GL.•-cancelʳ {g = M1 • K2345} {g' = K2345 • M1} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)}
    (trans (sym (move-product MV01953.proved (MV01954.proved))) (trans (cong refl R094.proved) (move-product MV01954.proved (MV01953.proved))))

module r2e_ij12346 where

  proved : M1 • K2346 ≈ K2346 • M1
  proved = GL.•-cancelʳ {g = M1 • K2346} {g' = K2346 • M1} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01955.proved (MV01956.proved))) (trans (cong refl R094.proved) (move-product MV01956.proved (MV01955.proved))))

module r2e_ij12347 where

  proved : M1 • K2347 ≈ K2347 • M1
  proved = GL.•-cancelʳ {g = M1 • K2347} {g' = K2347 • M1} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01957.proved (MV01958.proved))) (trans (cong refl R094.proved) (move-product MV01958.proved (MV01957.proved))))

module r2e_ij12356 where

  proved : M1 • K2356 ≈ K2356 • M1
  proved = GL.•-cancelʳ {g = M1 • K2356} {g' = K2356 • M1} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01959.proved (MV01960.proved))) (trans (cong refl R094.proved) (move-product MV01960.proved (MV01959.proved))))

module r2e_ij12357 where

  proved : M1 • K2357 ≈ K2357 • M1
  proved = GL.•-cancelʳ {g = M1 • K2357} {g' = K2357 • M1} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01961.proved (MV01962.proved))) (trans (cong refl R094.proved) (move-product MV01962.proved (MV01961.proved))))

module r2e_ij12367 where

  proved : M1 • K2367 ≈ K2367 • M1
  proved = GL.•-cancelʳ {g = M1 • K2367} {g' = K2367 • M1} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01963.proved (MV01964.proved))) (trans (cong refl R094.proved) (move-product MV01964.proved (MV01963.proved))))

module r2e_ij12456 where

  proved : M1 • K2456 ≈ K2456 • M1
  proved = GL.•-cancelʳ {g = M1 • K2456} {g' = K2456 • M1} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)}
    (trans (sym (move-product MV01965.proved (MV01966.proved))) (trans (cong refl R094.proved) (move-product MV01966.proved (MV01965.proved))))
