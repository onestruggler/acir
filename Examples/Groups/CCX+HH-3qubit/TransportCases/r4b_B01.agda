{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r4b_B01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M1 ; M2 ; M3 ; M4 ; X34 ; X35 ; X36 ; X45 ; X46 ; X56 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R098 as R098
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00631)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696 ; module MV00697 ; module MV00698 ; module MV00699 ; module MV00700 ; module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B074 using (module MV02924 ; module MV02925 ; module MV02926 ; module MV02927 ; module MV02928 ; module MV02929 ; module MV02930 ; module MV02931 ; module MV02932 ; module MV02933 ; module MV02934 ; module MV02935 ; module MV02936 ; module MV02937 ; module MV02938 ; module MV02939 ; module MV02940 ; module MV02941 ; module MV02942 ; module MV02943 ; module MV02944 ; module MV02945 ; module MV02946 ; module MV02947 ; module MV02948 ; module MV02949 ; module MV02950 ; module MV02951 ; module MV02952 ; module MV02953)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B075 using (module MV02954 ; module MV02955 ; module MV02956 ; module MV02957 ; module MV02958 ; module MV02959 ; module MV02960 ; module MV02961 ; module MV02962)

module r4b_ij1367 where

  proved : X36 • K1367 ≈ M1 • K1367 • M1 • K1367 • M1
  proved = GL.•-cancelʳ {g = X36 • K1367} {g' = M1 • K1367 • M1 • K1367 • M1} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02924.proved (MV00690.proved))) (trans (cong refl R098.proved) (move-product MV02925.proved (move-product MV00690.proved (move-product MV02925.proved (move-product MV00690.proved (MV02925.proved)))))))

module r4b_ij1456 where

  proved : X45 • K1456 ≈ M1 • K1456 • M1 • K1456 • M1
  proved = GL.•-cancelʳ {g = X45 • K1456} {g' = M1 • K1456 • M1 • K1456 • M1} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02926.proved (MV00691.proved))) (trans (cong refl R098.proved) (move-product MV02927.proved (move-product MV00691.proved (move-product MV02927.proved (move-product MV00691.proved (MV02927.proved)))))))

module r4b_ij1457 where

  proved : X45 • K1457 ≈ M1 • K1457 • M1 • K1457 • M1
  proved = GL.•-cancelʳ {g = X45 • K1457} {g' = M1 • K1457 • M1 • K1457 • M1} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02928.proved (MV00692.proved))) (trans (cong refl R098.proved) (move-product MV02929.proved (move-product MV00692.proved (move-product MV02929.proved (move-product MV00692.proved (MV02929.proved)))))))

module r4b_ij1467 where

  proved : X46 • K1467 ≈ M1 • K1467 • M1 • K1467 • M1
  proved = GL.•-cancelʳ {g = X46 • K1467} {g' = M1 • K1467 • M1 • K1467 • M1} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02930.proved (MV00693.proved))) (trans (cong refl R098.proved) (move-product MV02931.proved (move-product MV00693.proved (move-product MV02931.proved (move-product MV00693.proved (MV02931.proved)))))))

module r4b_ij1567 where

  proved : X56 • K1567 ≈ M1 • K1567 • M1 • K1567 • M1
  proved = GL.•-cancelʳ {g = X56 • K1567} {g' = M1 • K1567 • M1 • K1567 • M1} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02932.proved (MV00694.proved))) (trans (cong refl R098.proved) (move-product MV02933.proved (move-product MV00694.proved (move-product MV02933.proved (move-product MV00694.proved (MV02933.proved)))))))

module r4b_ij2345 where

  proved : X34 • K2345 ≈ M2 • K2345 • M2 • K2345 • M2
  proved = GL.•-cancelʳ {g = X34 • K2345} {g' = M2 • K2345 • M2 • K2345 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV02934.proved (MV00695.proved))) (trans (cong refl R098.proved) (move-product MV02935.proved (move-product MV00695.proved (move-product MV02935.proved (move-product MV00695.proved (MV02935.proved)))))))

module r4b_ij2346 where

  proved : X34 • K2346 ≈ M2 • K2346 • M2 • K2346 • M2
  proved = GL.•-cancelʳ {g = X34 • K2346} {g' = M2 • K2346 • M2 • K2346 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02936.proved (MV00696.proved))) (trans (cong refl R098.proved) (move-product MV02937.proved (move-product MV00696.proved (move-product MV02937.proved (move-product MV00696.proved (MV02937.proved)))))))

module r4b_ij2347 where

  proved : X34 • K2347 ≈ M2 • K2347 • M2 • K2347 • M2
  proved = GL.•-cancelʳ {g = X34 • K2347} {g' = M2 • K2347 • M2 • K2347 • M2} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02938.proved (MV00697.proved))) (trans (cong refl R098.proved) (move-product MV02939.proved (move-product MV00697.proved (move-product MV02939.proved (move-product MV00697.proved (MV02939.proved)))))))

module r4b_ij2356 where

  proved : X35 • K2356 ≈ M2 • K2356 • M2 • K2356 • M2
  proved = GL.•-cancelʳ {g = X35 • K2356} {g' = M2 • K2356 • M2 • K2356 • M2} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02940.proved (MV00698.proved))) (trans (cong refl R098.proved) (move-product MV02941.proved (move-product MV00698.proved (move-product MV02941.proved (move-product MV00698.proved (MV02941.proved)))))))

module r4b_ij2357 where

  proved : X35 • K2357 ≈ M2 • K2357 • M2 • K2357 • M2
  proved = GL.•-cancelʳ {g = X35 • K2357} {g' = M2 • K2357 • M2 • K2357 • M2} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02942.proved (MV00699.proved))) (trans (cong refl R098.proved) (move-product MV02943.proved (move-product MV00699.proved (move-product MV02943.proved (move-product MV00699.proved (MV02943.proved)))))))

module r4b_ij2367 where

  proved : X36 • K2367 ≈ M2 • K2367 • M2 • K2367 • M2
  proved = GL.•-cancelʳ {g = X36 • K2367} {g' = M2 • K2367 • M2 • K2367 • M2} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02944.proved (MV00700.proved))) (trans (cong refl R098.proved) (move-product MV02945.proved (move-product MV00700.proved (move-product MV02945.proved (move-product MV00700.proved (MV02945.proved)))))))

module r4b_ij2456 where

  proved : X45 • K2456 ≈ M2 • K2456 • M2 • K2456 • M2
  proved = GL.•-cancelʳ {g = X45 • K2456} {g' = M2 • K2456 • M2 • K2456 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02946.proved (MV00701.proved))) (trans (cong refl R098.proved) (move-product MV02947.proved (move-product MV00701.proved (move-product MV02947.proved (move-product MV00701.proved (MV02947.proved)))))))

module r4b_ij2457 where

  proved : X45 • K2457 ≈ M2 • K2457 • M2 • K2457 • M2
  proved = GL.•-cancelʳ {g = X45 • K2457} {g' = M2 • K2457 • M2 • K2457 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02948.proved (MV00702.proved))) (trans (cong refl R098.proved) (move-product MV02949.proved (move-product MV00702.proved (move-product MV02949.proved (move-product MV00702.proved (MV02949.proved)))))))

module r4b_ij2467 where

  proved : X46 • K2467 ≈ M2 • K2467 • M2 • K2467 • M2
  proved = GL.•-cancelʳ {g = X46 • K2467} {g' = M2 • K2467 • M2 • K2467 • M2} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02950.proved (MV00703.proved))) (trans (cong refl R098.proved) (move-product MV02951.proved (move-product MV00703.proved (move-product MV02951.proved (move-product MV00703.proved (MV02951.proved)))))))

module r4b_ij2567 where

  proved : X56 • K2567 ≈ M2 • K2567 • M2 • K2567 • M2
  proved = GL.•-cancelʳ {g = X56 • K2567} {g' = M2 • K2567 • M2 • K2567 • M2} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02952.proved (MV00704.proved))) (trans (cong refl R098.proved) (move-product MV02953.proved (move-product MV00704.proved (move-product MV02953.proved (move-product MV00704.proved (MV02953.proved)))))))

module r4b_ij3456 where

  proved : X45 • K3456 ≈ M3 • K3456 • M3 • K3456 • M3
  proved = GL.•-cancelʳ {g = X45 • K3456} {g' = M3 • K3456 • M3 • K3456 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV02954.proved (MV00705.proved))) (trans (cong refl R098.proved) (move-product MV02955.proved (move-product MV00705.proved (move-product MV02955.proved (move-product MV00705.proved (MV02955.proved)))))))

module r4b_ij3457 where

  proved : X45 • K3457 ≈ M3 • K3457 • M3 • K3457 • M3
  proved = GL.•-cancelʳ {g = X45 • K3457} {g' = M3 • K3457 • M3 • K3457 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02956.proved (MV00706.proved))) (trans (cong refl R098.proved) (move-product MV02957.proved (move-product MV00706.proved (move-product MV02957.proved (move-product MV00706.proved (MV02957.proved)))))))

module r4b_ij3467 where

  proved : X46 • K3467 ≈ M3 • K3467 • M3 • K3467 • M3
  proved = GL.•-cancelʳ {g = X46 • K3467} {g' = M3 • K3467 • M3 • K3467 • M3} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02958.proved (MV00707.proved))) (trans (cong refl R098.proved) (move-product MV02959.proved (move-product MV00707.proved (move-product MV02959.proved (move-product MV00707.proved (MV02959.proved)))))))

module r4b_ij3567 where

  proved : X56 • K3567 ≈ M3 • K3567 • M3 • K3567 • M3
  proved = GL.•-cancelʳ {g = X56 • K3567} {g' = M3 • K3567 • M3 • K3567 • M3} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02960.proved (MV00708.proved))) (trans (cong refl R098.proved) (move-product MV02961.proved (move-product MV00708.proved (move-product MV02961.proved (move-product MV00708.proved (MV02961.proved)))))))

module r4b_ij4567 where

  proved : X56 • K4567 ≈ M4 • K4567 • M4 • K4567 • M4
  proved = GL.•-cancelʳ {g = X56 • K4567} {g' = M4 • K4567 • M4 • K4567 • M4} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV02962.proved (MV00632.proved))) (trans (cong refl R098.proved) (move-product MV00631.proved (move-product MV00632.proved (move-product MV00631.proved (move-product MV00632.proved (MV00631.proved)))))))
