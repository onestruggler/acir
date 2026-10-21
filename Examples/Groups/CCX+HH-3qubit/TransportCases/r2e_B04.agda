{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_B04 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0126 ; K0134 ; K0135 ; K0136 ; K0145 ; K0146 ; K0156 ; K0234 ; K0235 ; K0236 ; K0245 ; K0246 ; K0256 ; K0345 ; K0346 ; K0356 ; K0456 ; K1234 ; K1235 ; K1236 ; K1245 ; K1246 ; K1256 ; K1345 ; K1346 ; K1356 ; K1456 ; K2345 ; K2346 ; K2356 ; K2456 ; K3456 ; M7 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B060 using (module MV02317 ; module MV02318 ; module MV02319 ; module MV02320 ; module MV02321 ; module MV02322 ; module MV02323 ; module MV02324)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B061 using (module MV02325 ; module MV02326 ; module MV02327 ; module MV02328 ; module MV02329 ; module MV02330 ; module MV02331 ; module MV02332 ; module MV02333 ; module MV02334 ; module MV02335 ; module MV02336 ; module MV02337 ; module MV02338 ; module MV02339 ; module MV02340 ; module MV02341 ; module MV02342 ; module MV02343 ; module MV02344 ; module MV02345 ; module MV02346 ; module MV02347 ; module MV02348 ; module MV02349 ; module MV02350 ; module MV02351 ; module MV02352 ; module MV02353 ; module MV02354 ; module MV02355 ; module MV02356 ; module MV02357 ; module MV02358 ; module MV02359 ; module MV02360 ; module MV02361 ; module MV02362 ; module MV02363 ; module MV02364)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B062 using (module MV02365 ; module MV02366 ; module MV02367 ; module MV02368 ; module MV02369 ; module MV02370 ; module MV02371 ; module MV02372 ; module MV02373 ; module MV02374 ; module MV02375 ; module MV02376 ; module MV02377 ; module MV02378 ; module MV02379 ; module MV02380)
open import Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 using (module R094)

module r2e_ij70126 where

  proved : M7 • K0126 ≈ K0126 • M7
  proved = GL.•-cancelʳ {g = M7 • K0126} {g' = K0126 • M7} {h = p (s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02317.proved (MV02318.proved))) (trans (cong refl R094.proved) (move-product MV02318.proved (MV02317.proved))))

module r2e_ij70134 where

  proved : M7 • K0134 ≈ K0134 • M7
  proved = GL.•-cancelʳ {g = M7 • K0134} {g' = K0134 • M7} {h = p (s2 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02319.proved (MV02320.proved))) (trans (cong refl R094.proved) (move-product MV02320.proved (MV02319.proved))))

module r2e_ij70135 where

  proved : M7 • K0135 ≈ K0135 • M7
  proved = GL.•-cancelʳ {g = M7 • K0135} {g' = K0135 • M7} {h = p (s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02321.proved (MV02322.proved))) (trans (cong refl R094.proved) (move-product MV02322.proved (MV02321.proved))))

module r2e_ij70136 where

  proved : M7 • K0136 ≈ K0136 • M7
  proved = GL.•-cancelʳ {g = M7 • K0136} {g' = K0136 • M7} {h = p (s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02323.proved (MV02324.proved))) (trans (cong refl R094.proved) (move-product MV02324.proved (MV02323.proved))))

module r2e_ij70145 where

  proved : M7 • K0145 ≈ K0145 • M7
  proved = GL.•-cancelʳ {g = M7 • K0145} {g' = K0145 • M7} {h = p (s3 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02325.proved (MV02326.proved))) (trans (cong refl R094.proved) (move-product MV02326.proved (MV02325.proved))))

module r2e_ij70146 where

  proved : M7 • K0146 ≈ K0146 • M7
  proved = GL.•-cancelʳ {g = M7 • K0146} {g' = K0146 • M7} {h = p (s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02327.proved (MV02328.proved))) (trans (cong refl R094.proved) (move-product MV02328.proved (MV02327.proved))))

module r2e_ij70156 where

  proved : M7 • K0156 ≈ K0156 • M7
  proved = GL.•-cancelʳ {g = M7 • K0156} {g' = K0156 • M7} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02329.proved (MV02330.proved))) (trans (cong refl R094.proved) (move-product MV02330.proved (MV02329.proved))))

module r2e_ij70234 where

  proved : M7 • K0234 ≈ K0234 • M7
  proved = GL.•-cancelʳ {g = M7 • K0234} {g' = K0234 • M7} {h = p (s1 • s2 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02331.proved (MV02332.proved))) (trans (cong refl R094.proved) (move-product MV02332.proved (MV02331.proved))))

module r2e_ij70235 where

  proved : M7 • K0235 ≈ K0235 • M7
  proved = GL.•-cancelʳ {g = M7 • K0235} {g' = K0235 • M7} {h = p (s1 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02333.proved (MV02334.proved))) (trans (cong refl R094.proved) (move-product MV02334.proved (MV02333.proved))))

module r2e_ij70236 where

  proved : M7 • K0236 ≈ K0236 • M7
  proved = GL.•-cancelʳ {g = M7 • K0236} {g' = K0236 • M7} {h = p (s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02335.proved (MV02336.proved))) (trans (cong refl R094.proved) (move-product MV02336.proved (MV02335.proved))))

module r2e_ij70245 where

  proved : M7 • K0245 ≈ K0245 • M7
  proved = GL.•-cancelʳ {g = M7 • K0245} {g' = K0245 • M7} {h = p (s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02337.proved (MV02338.proved))) (trans (cong refl R094.proved) (move-product MV02338.proved (MV02337.proved))))

module r2e_ij70246 where

  proved : M7 • K0246 ≈ K0246 • M7
  proved = GL.•-cancelʳ {g = M7 • K0246} {g' = K0246 • M7} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02339.proved (MV02340.proved))) (trans (cong refl R094.proved) (move-product MV02340.proved (MV02339.proved))))

module r2e_ij70256 where

  proved : M7 • K0256 ≈ K0256 • M7
  proved = GL.•-cancelʳ {g = M7 • K0256} {g' = K0256 • M7} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02341.proved (MV02342.proved))) (trans (cong refl R094.proved) (move-product MV02342.proved (MV02341.proved))))

module r2e_ij70345 where

  proved : M7 • K0345 ≈ K0345 • M7
  proved = GL.•-cancelʳ {g = M7 • K0345} {g' = K0345 • M7} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02343.proved (MV02344.proved))) (trans (cong refl R094.proved) (move-product MV02344.proved (MV02343.proved))))

module r2e_ij70346 where

  proved : M7 • K0346 ≈ K0346 • M7
  proved = GL.•-cancelʳ {g = M7 • K0346} {g' = K0346 • M7} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02345.proved (MV02346.proved))) (trans (cong refl R094.proved) (move-product MV02346.proved (MV02345.proved))))

module r2e_ij70356 where

  proved : M7 • K0356 ≈ K0356 • M7
  proved = GL.•-cancelʳ {g = M7 • K0356} {g' = K0356 • M7} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02347.proved (MV02348.proved))) (trans (cong refl R094.proved) (move-product MV02348.proved (MV02347.proved))))

module r2e_ij70456 where

  proved : M7 • K0456 ≈ K0456 • M7
  proved = GL.•-cancelʳ {g = M7 • K0456} {g' = K0456 • M7} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02349.proved (MV02350.proved))) (trans (cong refl R094.proved) (move-product MV02350.proved (MV02349.proved))))

module r2e_ij71234 where

  proved : M7 • K1234 ≈ K1234 • M7
  proved = GL.•-cancelʳ {g = M7 • K1234} {g' = K1234 • M7} {h = p (s0 • s1 • s2 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02351.proved (MV02352.proved))) (trans (cong refl R094.proved) (move-product MV02352.proved (MV02351.proved))))

module r2e_ij71235 where

  proved : M7 • K1235 ≈ K1235 • M7
  proved = GL.•-cancelʳ {g = M7 • K1235} {g' = K1235 • M7} {h = p (s0 • s1 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02353.proved (MV02354.proved))) (trans (cong refl R094.proved) (move-product MV02354.proved (MV02353.proved))))

module r2e_ij71236 where

  proved : M7 • K1236 ≈ K1236 • M7
  proved = GL.•-cancelʳ {g = M7 • K1236} {g' = K1236 • M7} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02355.proved (MV02356.proved))) (trans (cong refl R094.proved) (move-product MV02356.proved (MV02355.proved))))

module r2e_ij71245 where

  proved : M7 • K1245 ≈ K1245 • M7
  proved = GL.•-cancelʳ {g = M7 • K1245} {g' = K1245 • M7} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02357.proved (MV02358.proved))) (trans (cong refl R094.proved) (move-product MV02358.proved (MV02357.proved))))

module r2e_ij71246 where

  proved : M7 • K1246 ≈ K1246 • M7
  proved = GL.•-cancelʳ {g = M7 • K1246} {g' = K1246 • M7} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02359.proved (MV02360.proved))) (trans (cong refl R094.proved) (move-product MV02360.proved (MV02359.proved))))

module r2e_ij71256 where

  proved : M7 • K1256 ≈ K1256 • M7
  proved = GL.•-cancelʳ {g = M7 • K1256} {g' = K1256 • M7} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02361.proved (MV02362.proved))) (trans (cong refl R094.proved) (move-product MV02362.proved (MV02361.proved))))

module r2e_ij71345 where

  proved : M7 • K1345 ≈ K1345 • M7
  proved = GL.•-cancelʳ {g = M7 • K1345} {g' = K1345 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02363.proved (MV02364.proved))) (trans (cong refl R094.proved) (move-product MV02364.proved (MV02363.proved))))

module r2e_ij71346 where

  proved : M7 • K1346 ≈ K1346 • M7
  proved = GL.•-cancelʳ {g = M7 • K1346} {g' = K1346 • M7} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02365.proved (MV02366.proved))) (trans (cong refl R094.proved) (move-product MV02366.proved (MV02365.proved))))

module r2e_ij71356 where

  proved : M7 • K1356 ≈ K1356 • M7
  proved = GL.•-cancelʳ {g = M7 • K1356} {g' = K1356 • M7} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02367.proved (MV02368.proved))) (trans (cong refl R094.proved) (move-product MV02368.proved (MV02367.proved))))

module r2e_ij71456 where

  proved : M7 • K1456 ≈ K1456 • M7
  proved = GL.•-cancelʳ {g = M7 • K1456} {g' = K1456 • M7} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02369.proved (MV02370.proved))) (trans (cong refl R094.proved) (move-product MV02370.proved (MV02369.proved))))

module r2e_ij72345 where

  proved : M7 • K2345 ≈ K2345 • M7
  proved = GL.•-cancelʳ {g = M7 • K2345} {g' = K2345 • M7} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02371.proved (MV02372.proved))) (trans (cong refl R094.proved) (move-product MV02372.proved (MV02371.proved))))

module r2e_ij72346 where

  proved : M7 • K2346 ≈ K2346 • M7
  proved = GL.•-cancelʳ {g = M7 • K2346} {g' = K2346 • M7} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02373.proved (MV02374.proved))) (trans (cong refl R094.proved) (move-product MV02374.proved (MV02373.proved))))

module r2e_ij72356 where

  proved : M7 • K2356 ≈ K2356 • M7
  proved = GL.•-cancelʳ {g = M7 • K2356} {g' = K2356 • M7} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02375.proved (MV02376.proved))) (trans (cong refl R094.proved) (move-product MV02376.proved (MV02375.proved))))

module r2e_ij72456 where

  proved : M7 • K2456 ≈ K2456 • M7
  proved = GL.•-cancelʳ {g = M7 • K2456} {g' = K2456 • M7} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02377.proved (MV02378.proved))) (trans (cong refl R094.proved) (move-product MV02378.proved (MV02377.proved))))

module r2e_ij73456 where

  proved : M7 • K3456 ≈ K3456 • M7
  proved = GL.•-cancelʳ {g = M7 • K3456} {g' = K3456 • M7} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02379.proved (MV02380.proved))) (trans (cong refl R094.proved) (move-product MV02380.proved (MV02379.proved))))
