{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2f_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans ; ε)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 as R096
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00629 ; module MV00641 ; module MV00642 ; module MV00643)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00644 ; module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654 ; module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00659 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664 ; module MV00665 ; module MV00666 ; module MV00667 ; module MV00668 ; module MV00669 ; module MV00670 ; module MV00671 ; module MV00672 ; module MV00673 ; module MV00674 ; module MV00675 ; module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684 ; module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689 ; module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696 ; module MV00697 ; module MV00698 ; module MV00699 ; module MV00700)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B062 using (module MV02381 ; module MV02382 ; module MV02383 ; module MV02384 ; module MV02385 ; module MV02386 ; module MV02387 ; module MV02388 ; module MV02389 ; module MV02390 ; module MV02391 ; module MV02392 ; module MV02393 ; module MV02394 ; module MV02395 ; module MV02396 ; module MV02397 ; module MV02398 ; module MV02399 ; module MV02400 ; module MV02401 ; module MV02402 ; module MV02403 ; module MV02404 ; module MV02405)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B063 using (module MV02406 ; module MV02407 ; module MV02408 ; module MV02409 ; module MV02410 ; module MV02411 ; module MV02412 ; module MV02413 ; module MV02414 ; module MV02415 ; module MV02416 ; module MV02417 ; module MV02418 ; module MV02419 ; module MV02420 ; module MV02421 ; module MV02422 ; module MV02423 ; module MV02424 ; module MV02425 ; module MV02426 ; module MV02427 ; module MV02428 ; module MV02429 ; module MV02430 ; module MV02431 ; module MV02432 ; module MV02433 ; module MV02434 ; module MV02435 ; module MV02436 ; module MV02437 ; module MV02438 ; module MV02439 ; module MV02440)

module r2f_ij01234567 where

  proved : K0123 • K4567 ≈ K4567 • K0123
  proved = GL.•-cancelʳ {g = K0123 • K4567} {g' = K4567 • K0123} {h = p (ε)}
    (trans (sym (move-product MV00641.proved (MV02381.proved))) (trans (cong refl R096.proved) (move-product MV02381.proved (MV00641.proved))))

module r2f_ij01243567 where

  proved : K0124 • K3567 ≈ K3567 • K0124
  proved = GL.•-cancelʳ {g = K0124 • K3567} {g' = K3567 • K0124} {h = p (s3)}
    (trans (sym (move-product MV00245.proved (MV00629.proved))) (trans (cong refl R096.proved) (move-product MV00629.proved (MV00245.proved))))

module r2f_ij01253467 where

  proved : K0125 • K3467 ≈ K3467 • K0125
  proved = GL.•-cancelʳ {g = K0125 • K3467} {g' = K3467 • K0125} {h = p (s4 • s3)}
    (trans (sym (move-product MV00642.proved (MV02382.proved))) (trans (cong refl R096.proved) (move-product MV02382.proved (MV00642.proved))))

module r2f_ij01263457 where

  proved : K0126 • K3457 ≈ K3457 • K0126
  proved = GL.•-cancelʳ {g = K0126 • K3457} {g' = K3457 • K0126} {h = p (s5 • s4 • s3)}
    (trans (sym (move-product MV00643.proved (MV02383.proved))) (trans (cong refl R096.proved) (move-product MV02383.proved (MV00643.proved))))

module r2f_ij01273456 where

  proved : K0127 • K3456 ≈ K3456 • K0127
  proved = GL.•-cancelʳ {g = K0127 • K3456} {g' = K3456 • K0127} {h = p (s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00644.proved (MV02384.proved))) (trans (cong refl R096.proved) (move-product MV02384.proved (MV00644.proved))))

module r2f_ij01342567 where

  proved : K0134 • K2567 ≈ K2567 • K0134
  proved = GL.•-cancelʳ {g = K0134 • K2567} {g' = K2567 • K0134} {h = p (s2 • s3)}
    (trans (sym (move-product MV00645.proved (MV02385.proved))) (trans (cong refl R096.proved) (move-product MV02385.proved (MV00645.proved))))

module r2f_ij01352467 where

  proved : K0135 • K2467 ≈ K2467 • K0135
  proved = GL.•-cancelʳ {g = K0135 • K2467} {g' = K2467 • K0135} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV00646.proved (MV02386.proved))) (trans (cong refl R096.proved) (move-product MV02386.proved (MV00646.proved))))

module r2f_ij01362457 where

  proved : K0136 • K2457 ≈ K2457 • K0136
  proved = GL.•-cancelʳ {g = K0136 • K2457} {g' = K2457 • K0136} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00647.proved (MV02387.proved))) (trans (cong refl R096.proved) (move-product MV02387.proved (MV00647.proved))))

module r2f_ij01372456 where

  proved : K0137 • K2456 ≈ K2456 • K0137
  proved = GL.•-cancelʳ {g = K0137 • K2456} {g' = K2456 • K0137} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00648.proved (MV02388.proved))) (trans (cong refl R096.proved) (move-product MV02388.proved (MV00648.proved))))

module r2f_ij01452367 where

  proved : K0145 • K2367 ≈ K2367 • K0145
  proved = GL.•-cancelʳ {g = K0145 • K2367} {g' = K2367 • K0145} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00649.proved (MV02389.proved))) (trans (cong refl R096.proved) (move-product MV02389.proved (MV00649.proved))))

module r2f_ij01462357 where

  proved : K0146 • K2357 ≈ K2357 • K0146
  proved = GL.•-cancelʳ {g = K0146 • K2357} {g' = K2357 • K0146} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00650.proved (MV02390.proved))) (trans (cong refl R096.proved) (move-product MV02390.proved (MV00650.proved))))

module r2f_ij01472356 where

  proved : K0147 • K2356 ≈ K2356 • K0147
  proved = GL.•-cancelʳ {g = K0147 • K2356} {g' = K2356 • K0147} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00651.proved (MV02391.proved))) (trans (cong refl R096.proved) (move-product MV02391.proved (MV00651.proved))))

module r2f_ij01562347 where

  proved : K0156 • K2347 ≈ K2347 • K0156
  proved = GL.•-cancelʳ {g = K0156 • K2347} {g' = K2347 • K0156} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00652.proved (MV02392.proved))) (trans (cong refl R096.proved) (move-product MV02392.proved (MV00652.proved))))

module r2f_ij01572346 where

  proved : K0157 • K2346 ≈ K2346 • K0157
  proved = GL.•-cancelʳ {g = K0157 • K2346} {g' = K2346 • K0157} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00653.proved (MV02393.proved))) (trans (cong refl R096.proved) (move-product MV02393.proved (MV00653.proved))))

module r2f_ij01672345 where

  proved : K0167 • K2345 ≈ K2345 • K0167
  proved = GL.•-cancelʳ {g = K0167 • K2345} {g' = K2345 • K0167} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00654.proved (MV02394.proved))) (trans (cong refl R096.proved) (move-product MV02394.proved (MV00654.proved))))

module r2f_ij02341567 where

  proved : K0234 • K1567 ≈ K1567 • K0234
  proved = GL.•-cancelʳ {g = K0234 • K1567} {g' = K1567 • K0234} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV00655.proved (MV02395.proved))) (trans (cong refl R096.proved) (move-product MV02395.proved (MV00655.proved))))

module r2f_ij02351467 where

  proved : K0235 • K1467 ≈ K1467 • K0235
  proved = GL.•-cancelʳ {g = K0235 • K1467} {g' = K1467 • K0235} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV00656.proved (MV02396.proved))) (trans (cong refl R096.proved) (move-product MV02396.proved (MV00656.proved))))

module r2f_ij02361457 where

  proved : K0236 • K1457 ≈ K1457 • K0236
  proved = GL.•-cancelʳ {g = K0236 • K1457} {g' = K1457 • K0236} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00657.proved (MV02397.proved))) (trans (cong refl R096.proved) (move-product MV02397.proved (MV00657.proved))))

module r2f_ij02371456 where

  proved : K0237 • K1456 ≈ K1456 • K0237
  proved = GL.•-cancelʳ {g = K0237 • K1456} {g' = K1456 • K0237} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00658.proved (MV02398.proved))) (trans (cong refl R096.proved) (move-product MV02398.proved (MV00658.proved))))

module r2f_ij02451367 where

  proved : K0245 • K1367 ≈ K1367 • K0245
  proved = GL.•-cancelʳ {g = K0245 • K1367} {g' = K1367 • K0245} {h = p (s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00659.proved (MV02399.proved))) (trans (cong refl R096.proved) (move-product MV02399.proved (MV00659.proved))))

module r2f_ij02461357 where

  proved : K0246 • K1357 ≈ K1357 • K0246
  proved = GL.•-cancelʳ {g = K0246 • K1357} {g' = K1357 • K0246} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00660.proved (MV02400.proved))) (trans (cong refl R096.proved) (move-product MV02400.proved (MV00660.proved))))

module r2f_ij02471356 where

  proved : K0247 • K1356 ≈ K1356 • K0247
  proved = GL.•-cancelʳ {g = K0247 • K1356} {g' = K1356 • K0247} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00661.proved (MV02401.proved))) (trans (cong refl R096.proved) (move-product MV02401.proved (MV00661.proved))))

module r2f_ij02561347 where

  proved : K0256 • K1347 ≈ K1347 • K0256
  proved = GL.•-cancelʳ {g = K0256 • K1347} {g' = K1347 • K0256} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00662.proved (MV02402.proved))) (trans (cong refl R096.proved) (move-product MV02402.proved (MV00662.proved))))

module r2f_ij02571346 where

  proved : K0257 • K1346 ≈ K1346 • K0257
  proved = GL.•-cancelʳ {g = K0257 • K1346} {g' = K1346 • K0257} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00663.proved (MV02403.proved))) (trans (cong refl R096.proved) (move-product MV02403.proved (MV00663.proved))))

module r2f_ij02671345 where

  proved : K0267 • K1345 ≈ K1345 • K0267
  proved = GL.•-cancelʳ {g = K0267 • K1345} {g' = K1345 • K0267} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00664.proved (MV02404.proved))) (trans (cong refl R096.proved) (move-product MV02404.proved (MV00664.proved))))

module r2f_ij03451267 where

  proved : K0345 • K1267 ≈ K1267 • K0345
  proved = GL.•-cancelʳ {g = K0345 • K1267} {g' = K1267 • K0345} {h = p (s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00665.proved (MV02405.proved))) (trans (cong refl R096.proved) (move-product MV02405.proved (MV00665.proved))))

module r2f_ij03461257 where

  proved : K0346 • K1257 ≈ K1257 • K0346
  proved = GL.•-cancelʳ {g = K0346 • K1257} {g' = K1257 • K0346} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00666.proved (MV02406.proved))) (trans (cong refl R096.proved) (move-product MV02406.proved (MV00666.proved))))

module r2f_ij03471256 where

  proved : K0347 • K1256 ≈ K1256 • K0347
  proved = GL.•-cancelʳ {g = K0347 • K1256} {g' = K1256 • K0347} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00667.proved (MV02407.proved))) (trans (cong refl R096.proved) (move-product MV02407.proved (MV00667.proved))))

module r2f_ij03561247 where

  proved : K0356 • K1247 ≈ K1247 • K0356
  proved = GL.•-cancelʳ {g = K0356 • K1247} {g' = K1247 • K0356} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00668.proved (MV02408.proved))) (trans (cong refl R096.proved) (move-product MV02408.proved (MV00668.proved))))

module r2f_ij03571246 where

  proved : K0357 • K1246 ≈ K1246 • K0357
  proved = GL.•-cancelʳ {g = K0357 • K1246} {g' = K1246 • K0357} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00669.proved (MV02409.proved))) (trans (cong refl R096.proved) (move-product MV02409.proved (MV00669.proved))))

module r2f_ij03671245 where

  proved : K0367 • K1245 ≈ K1245 • K0367
  proved = GL.•-cancelʳ {g = K0367 • K1245} {g' = K1245 • K0367} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00670.proved (MV02410.proved))) (trans (cong refl R096.proved) (move-product MV02410.proved (MV00670.proved))))

module r2f_ij04561237 where

  proved : K0456 • K1237 ≈ K1237 • K0456
  proved = GL.•-cancelʳ {g = K0456 • K1237} {g' = K1237 • K0456} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00671.proved (MV02411.proved))) (trans (cong refl R096.proved) (move-product MV02411.proved (MV00671.proved))))

module r2f_ij04571236 where

  proved : K0457 • K1236 ≈ K1236 • K0457
  proved = GL.•-cancelʳ {g = K0457 • K1236} {g' = K1236 • K0457} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00672.proved (MV02412.proved))) (trans (cong refl R096.proved) (move-product MV02412.proved (MV00672.proved))))

module r2f_ij04671235 where

  proved : K0467 • K1235 ≈ K1235 • K0467
  proved = GL.•-cancelʳ {g = K0467 • K1235} {g' = K1235 • K0467} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00673.proved (MV02413.proved))) (trans (cong refl R096.proved) (move-product MV02413.proved (MV00673.proved))))

module r2f_ij05671234 where

  proved : K0567 • K1234 ≈ K1234 • K0567
  proved = GL.•-cancelʳ {g = K0567 • K1234} {g' = K1234 • K0567} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00674.proved (MV02414.proved))) (trans (cong refl R096.proved) (move-product MV02414.proved (MV00674.proved))))

module r2f_ij12340567 where

  proved : K1234 • K0567 ≈ K0567 • K1234
  proved = GL.•-cancelʳ {g = K1234 • K0567} {g' = K0567 • K1234} {h = p (s0 • s1 • s2 • s3)}
    (trans (sym (move-product MV00675.proved (MV02415.proved))) (trans (cong refl R096.proved) (move-product MV02415.proved (MV00675.proved))))

module r2f_ij12350467 where

  proved : K1235 • K0467 ≈ K0467 • K1235
  proved = GL.•-cancelʳ {g = K1235 • K0467} {g' = K0467 • K1235} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV00676.proved (MV02416.proved))) (trans (cong refl R096.proved) (move-product MV02416.proved (MV00676.proved))))

module r2f_ij12360457 where

  proved : K1236 • K0457 ≈ K0457 • K1236
  proved = GL.•-cancelʳ {g = K1236 • K0457} {g' = K0457 • K1236} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00677.proved (MV02417.proved))) (trans (cong refl R096.proved) (move-product MV02417.proved (MV00677.proved))))

module r2f_ij12370456 where

  proved : K1237 • K0456 ≈ K0456 • K1237
  proved = GL.•-cancelʳ {g = K1237 • K0456} {g' = K0456 • K1237} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00678.proved (MV02418.proved))) (trans (cong refl R096.proved) (move-product MV02418.proved (MV00678.proved))))

module r2f_ij12450367 where

  proved : K1245 • K0367 ≈ K0367 • K1245
  proved = GL.•-cancelʳ {g = K1245 • K0367} {g' = K0367 • K1245} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00679.proved (MV02419.proved))) (trans (cong refl R096.proved) (move-product MV02419.proved (MV00679.proved))))

module r2f_ij12460357 where

  proved : K1246 • K0357 ≈ K0357 • K1246
  proved = GL.•-cancelʳ {g = K1246 • K0357} {g' = K0357 • K1246} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00680.proved (MV02420.proved))) (trans (cong refl R096.proved) (move-product MV02420.proved (MV00680.proved))))

module r2f_ij12470356 where

  proved : K1247 • K0356 ≈ K0356 • K1247
  proved = GL.•-cancelʳ {g = K1247 • K0356} {g' = K0356 • K1247} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00681.proved (MV02421.proved))) (trans (cong refl R096.proved) (move-product MV02421.proved (MV00681.proved))))

module r2f_ij12560347 where

  proved : K1256 • K0347 ≈ K0347 • K1256
  proved = GL.•-cancelʳ {g = K1256 • K0347} {g' = K0347 • K1256} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00682.proved (MV02422.proved))) (trans (cong refl R096.proved) (move-product MV02422.proved (MV00682.proved))))

module r2f_ij12570346 where

  proved : K1257 • K0346 ≈ K0346 • K1257
  proved = GL.•-cancelʳ {g = K1257 • K0346} {g' = K0346 • K1257} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00683.proved (MV02423.proved))) (trans (cong refl R096.proved) (move-product MV02423.proved (MV00683.proved))))

module r2f_ij12670345 where

  proved : K1267 • K0345 ≈ K0345 • K1267
  proved = GL.•-cancelʳ {g = K1267 • K0345} {g' = K0345 • K1267} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00684.proved (MV02424.proved))) (trans (cong refl R096.proved) (move-product MV02424.proved (MV00684.proved))))

module r2f_ij13450267 where

  proved : K1345 • K0267 ≈ K0267 • K1345
  proved = GL.•-cancelʳ {g = K1345 • K0267} {g' = K0267 • K1345} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00685.proved (MV02425.proved))) (trans (cong refl R096.proved) (move-product MV02425.proved (MV00685.proved))))

module r2f_ij13460257 where

  proved : K1346 • K0257 ≈ K0257 • K1346
  proved = GL.•-cancelʳ {g = K1346 • K0257} {g' = K0257 • K1346} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00686.proved (MV02426.proved))) (trans (cong refl R096.proved) (move-product MV02426.proved (MV00686.proved))))

module r2f_ij13470256 where

  proved : K1347 • K0256 ≈ K0256 • K1347
  proved = GL.•-cancelʳ {g = K1347 • K0256} {g' = K0256 • K1347} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00687.proved (MV02427.proved))) (trans (cong refl R096.proved) (move-product MV02427.proved (MV00687.proved))))

module r2f_ij13560247 where

  proved : K1356 • K0247 ≈ K0247 • K1356
  proved = GL.•-cancelʳ {g = K1356 • K0247} {g' = K0247 • K1356} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00688.proved (MV02428.proved))) (trans (cong refl R096.proved) (move-product MV02428.proved (MV00688.proved))))

module r2f_ij13570246 where

  proved : K1357 • K0246 ≈ K0246 • K1357
  proved = GL.•-cancelʳ {g = K1357 • K0246} {g' = K0246 • K1357} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00689.proved (MV02429.proved))) (trans (cong refl R096.proved) (move-product MV02429.proved (MV00689.proved))))

module r2f_ij13670245 where

  proved : K1367 • K0245 ≈ K0245 • K1367
  proved = GL.•-cancelʳ {g = K1367 • K0245} {g' = K0245 • K1367} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00690.proved (MV02430.proved))) (trans (cong refl R096.proved) (move-product MV02430.proved (MV00690.proved))))

module r2f_ij14560237 where

  proved : K1456 • K0237 ≈ K0237 • K1456
  proved = GL.•-cancelʳ {g = K1456 • K0237} {g' = K0237 • K1456} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00691.proved (MV02431.proved))) (trans (cong refl R096.proved) (move-product MV02431.proved (MV00691.proved))))

module r2f_ij14570236 where

  proved : K1457 • K0236 ≈ K0236 • K1457
  proved = GL.•-cancelʳ {g = K1457 • K0236} {g' = K0236 • K1457} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00692.proved (MV02432.proved))) (trans (cong refl R096.proved) (move-product MV02432.proved (MV00692.proved))))

module r2f_ij14670235 where

  proved : K1467 • K0235 ≈ K0235 • K1467
  proved = GL.•-cancelʳ {g = K1467 • K0235} {g' = K0235 • K1467} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00693.proved (MV02433.proved))) (trans (cong refl R096.proved) (move-product MV02433.proved (MV00693.proved))))

module r2f_ij15670234 where

  proved : K1567 • K0234 ≈ K0234 • K1567
  proved = GL.•-cancelʳ {g = K1567 • K0234} {g' = K0234 • K1567} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00694.proved (MV02434.proved))) (trans (cong refl R096.proved) (move-product MV02434.proved (MV00694.proved))))

module r2f_ij23450167 where

  proved : K2345 • K0167 ≈ K0167 • K2345
  proved = GL.•-cancelʳ {g = K2345 • K0167} {g' = K0167 • K2345} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV00695.proved (MV02435.proved))) (trans (cong refl R096.proved) (move-product MV02435.proved (MV00695.proved))))

module r2f_ij23460157 where

  proved : K2346 • K0157 ≈ K0157 • K2346
  proved = GL.•-cancelʳ {g = K2346 • K0157} {g' = K0157 • K2346} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00696.proved (MV02436.proved))) (trans (cong refl R096.proved) (move-product MV02436.proved (MV00696.proved))))

module r2f_ij23470156 where

  proved : K2347 • K0156 ≈ K0156 • K2347
  proved = GL.•-cancelʳ {g = K2347 • K0156} {g' = K0156 • K2347} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00697.proved (MV02437.proved))) (trans (cong refl R096.proved) (move-product MV02437.proved (MV00697.proved))))

module r2f_ij23560147 where

  proved : K2356 • K0147 ≈ K0147 • K2356
  proved = GL.•-cancelʳ {g = K2356 • K0147} {g' = K0147 • K2356} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV00698.proved (MV02438.proved))) (trans (cong refl R096.proved) (move-product MV02438.proved (MV00698.proved))))

module r2f_ij23570146 where

  proved : K2357 • K0146 ≈ K0146 • K2357
  proved = GL.•-cancelʳ {g = K2357 • K0146} {g' = K0146 • K2357} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00699.proved (MV02439.proved))) (trans (cong refl R096.proved) (move-product MV02439.proved (MV00699.proved))))

module r2f_ij23670145 where

  proved : K2367 • K0145 ≈ K0145 • K2367
  proved = GL.•-cancelʳ {g = K2367 • K0145} {g' = K0145 • K2367} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV00700.proved (MV02440.proved))) (trans (cong refl R096.proved) (move-product MV02440.proved (MV00700.proved))))
