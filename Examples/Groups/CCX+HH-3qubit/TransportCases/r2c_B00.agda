{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B00 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; X01 ; X02 ; X03 ; X04 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as R091
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00632)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00676 ; module MV00677 ; module MV00678 ; module MV00679 ; module MV00680 ; module MV00681 ; module MV00682 ; module MV00683 ; module MV00684 ; module MV00685 ; module MV00686 ; module MV00687 ; module MV00688 ; module MV00689 ; module MV00690)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 using (module MV00691 ; module MV00692 ; module MV00693 ; module MV00694 ; module MV00695 ; module MV00696 ; module MV00697 ; module MV00698 ; module MV00699 ; module MV00700 ; module MV00701 ; module MV00702 ; module MV00703 ; module MV00704 ; module MV00705 ; module MV00706 ; module MV00707 ; module MV00708)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B026 using (module MV01034 ; module MV01035 ; module MV01036 ; module MV01037 ; module MV01038 ; module MV01039 ; module MV01040 ; module MV01041 ; module MV01042 ; module MV01043 ; module MV01044 ; module MV01045 ; module MV01046 ; module MV01047 ; module MV01048 ; module MV01049 ; module MV01050 ; module MV01051)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B027 using (module MV01052 ; module MV01053 ; module MV01054 ; module MV01055 ; module MV01056 ; module MV01057 ; module MV01058 ; module MV01059 ; module MV01060 ; module MV01061 ; module MV01062 ; module MV01063 ; module MV01064 ; module MV01065 ; module MV01066 ; module MV01067 ; module MV01068 ; module MV01069 ; module MV01070 ; module MV01071 ; module MV01072 ; module MV01073 ; module MV01074 ; module MV01075 ; module MV01076 ; module MV01077 ; module MV01078 ; module MV01079 ; module MV01080 ; module MV01081 ; module MV01082 ; module MV01083)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B028 using (module MV01084 ; module MV01085 ; module MV01086 ; module MV01087 ; module MV01088 ; module MV01089 ; module MV01090 ; module MV01091 ; module MV01092 ; module MV01093 ; module MV01094 ; module MV01095 ; module MV01096 ; module MV01097 ; module MV01098 ; module MV01099 ; module MV01100 ; module MV01101 ; module MV01102 ; module MV01103 ; module MV01104 ; module MV01105 ; module MV01106 ; module MV01107 ; module MV01108 ; module MV01109 ; module MV01110 ; module MV01111 ; module MV01112 ; module MV01113 ; module MV01114 ; module MV01115)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B029 using (module MV01116 ; module MV01117 ; module MV01118 ; module MV01119)

module r2c_ij012345 where

  proved : X01 • K2345 ≈ K2345 • X01
  proved = GL.•-cancelʳ {g = X01 • K2345} {g' = K2345 • X01} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01034.proved (MV00695.proved))) (trans (cong refl R091.proved) (move-product MV00695.proved (MV01034.proved))))

module r2c_ij012346 where

  proved : X01 • K2346 ≈ K2346 • X01
  proved = GL.•-cancelʳ {g = X01 • K2346} {g' = K2346 • X01} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01035.proved (MV00696.proved))) (trans (cong refl R091.proved) (move-product MV00696.proved (MV01035.proved))))

module r2c_ij012347 where

  proved : X01 • K2347 ≈ K2347 • X01
  proved = GL.•-cancelʳ {g = X01 • K2347} {g' = K2347 • X01} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01036.proved (MV00697.proved))) (trans (cong refl R091.proved) (move-product MV00697.proved (MV01036.proved))))

module r2c_ij012356 where

  proved : X01 • K2356 ≈ K2356 • X01
  proved = GL.•-cancelʳ {g = X01 • K2356} {g' = K2356 • X01} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01037.proved (MV00698.proved))) (trans (cong refl R091.proved) (move-product MV00698.proved (MV01037.proved))))

module r2c_ij012357 where

  proved : X01 • K2357 ≈ K2357 • X01
  proved = GL.•-cancelʳ {g = X01 • K2357} {g' = K2357 • X01} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01038.proved (MV00699.proved))) (trans (cong refl R091.proved) (move-product MV00699.proved (MV01038.proved))))

module r2c_ij012367 where

  proved : X01 • K2367 ≈ K2367 • X01
  proved = GL.•-cancelʳ {g = X01 • K2367} {g' = K2367 • X01} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01039.proved (MV00700.proved))) (trans (cong refl R091.proved) (move-product MV00700.proved (MV01039.proved))))

module r2c_ij012456 where

  proved : X01 • K2456 ≈ K2456 • X01
  proved = GL.•-cancelʳ {g = X01 • K2456} {g' = K2456 • X01} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01040.proved (MV00701.proved))) (trans (cong refl R091.proved) (move-product MV00701.proved (MV01040.proved))))

module r2c_ij012457 where

  proved : X01 • K2457 ≈ K2457 • X01
  proved = GL.•-cancelʳ {g = X01 • K2457} {g' = K2457 • X01} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01041.proved (MV00702.proved))) (trans (cong refl R091.proved) (move-product MV00702.proved (MV01041.proved))))

module r2c_ij012467 where

  proved : X01 • K2467 ≈ K2467 • X01
  proved = GL.•-cancelʳ {g = X01 • K2467} {g' = K2467 • X01} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01042.proved (MV00703.proved))) (trans (cong refl R091.proved) (move-product MV00703.proved (MV01042.proved))))

module r2c_ij012567 where

  proved : X01 • K2567 ≈ K2567 • X01
  proved = GL.•-cancelʳ {g = X01 • K2567} {g' = K2567 • X01} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01043.proved (MV00704.proved))) (trans (cong refl R091.proved) (move-product MV00704.proved (MV01043.proved))))

module r2c_ij013456 where

  proved : X01 • K3456 ≈ K3456 • X01
  proved = GL.•-cancelʳ {g = X01 • K3456} {g' = K3456 • X01} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01044.proved (MV00705.proved))) (trans (cong refl R091.proved) (move-product MV00705.proved (MV01044.proved))))

module r2c_ij013457 where

  proved : X01 • K3457 ≈ K3457 • X01
  proved = GL.•-cancelʳ {g = X01 • K3457} {g' = K3457 • X01} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01045.proved (MV00706.proved))) (trans (cong refl R091.proved) (move-product MV00706.proved (MV01045.proved))))

module r2c_ij013467 where

  proved : X01 • K3467 ≈ K3467 • X01
  proved = GL.•-cancelʳ {g = X01 • K3467} {g' = K3467 • X01} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01046.proved (MV00707.proved))) (trans (cong refl R091.proved) (move-product MV00707.proved (MV01046.proved))))

module r2c_ij013567 where

  proved : X01 • K3567 ≈ K3567 • X01
  proved = GL.•-cancelʳ {g = X01 • K3567} {g' = K3567 • X01} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01047.proved (MV00708.proved))) (trans (cong refl R091.proved) (move-product MV00708.proved (MV01047.proved))))

module r2c_ij014567 where

  proved : X01 • K4567 ≈ K4567 • X01
  proved = GL.•-cancelʳ {g = X01 • K4567} {g' = K4567 • X01} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01048.proved (MV00632.proved))) (trans (cong refl R091.proved) (move-product MV00632.proved (MV01048.proved))))

module r2c_ij021345 where

  proved : X02 • K1345 ≈ K1345 • X02
  proved = GL.•-cancelʳ {g = X02 • K1345} {g' = K1345 • X02} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01049.proved (MV00685.proved))) (trans (cong refl R091.proved) (move-product MV00685.proved (MV01049.proved))))

module r2c_ij021346 where

  proved : X02 • K1346 ≈ K1346 • X02
  proved = GL.•-cancelʳ {g = X02 • K1346} {g' = K1346 • X02} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01050.proved (MV00686.proved))) (trans (cong refl R091.proved) (move-product MV00686.proved (MV01050.proved))))

module r2c_ij021347 where

  proved : X02 • K1347 ≈ K1347 • X02
  proved = GL.•-cancelʳ {g = X02 • K1347} {g' = K1347 • X02} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01051.proved (MV00687.proved))) (trans (cong refl R091.proved) (move-product MV00687.proved (MV01051.proved))))

module r2c_ij021356 where

  proved : X02 • K1356 ≈ K1356 • X02
  proved = GL.•-cancelʳ {g = X02 • K1356} {g' = K1356 • X02} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01052.proved (MV00688.proved))) (trans (cong refl R091.proved) (move-product MV00688.proved (MV01052.proved))))

module r2c_ij021357 where

  proved : X02 • K1357 ≈ K1357 • X02
  proved = GL.•-cancelʳ {g = X02 • K1357} {g' = K1357 • X02} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01053.proved (MV00689.proved))) (trans (cong refl R091.proved) (move-product MV00689.proved (MV01053.proved))))

module r2c_ij021367 where

  proved : X02 • K1367 ≈ K1367 • X02
  proved = GL.•-cancelʳ {g = X02 • K1367} {g' = K1367 • X02} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01054.proved (MV00690.proved))) (trans (cong refl R091.proved) (move-product MV00690.proved (MV01054.proved))))

module r2c_ij021456 where

  proved : X02 • K1456 ≈ K1456 • X02
  proved = GL.•-cancelʳ {g = X02 • K1456} {g' = K1456 • X02} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01055.proved (MV00691.proved))) (trans (cong refl R091.proved) (move-product MV00691.proved (MV01055.proved))))

module r2c_ij021457 where

  proved : X02 • K1457 ≈ K1457 • X02
  proved = GL.•-cancelʳ {g = X02 • K1457} {g' = K1457 • X02} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01056.proved (MV00692.proved))) (trans (cong refl R091.proved) (move-product MV00692.proved (MV01056.proved))))

module r2c_ij021467 where

  proved : X02 • K1467 ≈ K1467 • X02
  proved = GL.•-cancelʳ {g = X02 • K1467} {g' = K1467 • X02} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01057.proved (MV00693.proved))) (trans (cong refl R091.proved) (move-product MV00693.proved (MV01057.proved))))

module r2c_ij021567 where

  proved : X02 • K1567 ≈ K1567 • X02
  proved = GL.•-cancelʳ {g = X02 • K1567} {g' = K1567 • X02} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01058.proved (MV00694.proved))) (trans (cong refl R091.proved) (move-product MV00694.proved (MV01058.proved))))

module r2c_ij023456 where

  proved : X02 • K3456 ≈ K3456 • X02
  proved = GL.•-cancelʳ {g = X02 • K3456} {g' = K3456 • X02} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01059.proved (MV01060.proved))) (trans (cong refl R091.proved) (move-product MV01060.proved (MV01059.proved))))

module r2c_ij023457 where

  proved : X02 • K3457 ≈ K3457 • X02
  proved = GL.•-cancelʳ {g = X02 • K3457} {g' = K3457 • X02} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01061.proved (MV01062.proved))) (trans (cong refl R091.proved) (move-product MV01062.proved (MV01061.proved))))

module r2c_ij023467 where

  proved : X02 • K3467 ≈ K3467 • X02
  proved = GL.•-cancelʳ {g = X02 • K3467} {g' = K3467 • X02} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01063.proved (MV01064.proved))) (trans (cong refl R091.proved) (move-product MV01064.proved (MV01063.proved))))

module r2c_ij023567 where

  proved : X02 • K3567 ≈ K3567 • X02
  proved = GL.•-cancelʳ {g = X02 • K3567} {g' = K3567 • X02} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01065.proved (MV01066.proved))) (trans (cong refl R091.proved) (move-product MV01066.proved (MV01065.proved))))

module r2c_ij024567 where

  proved : X02 • K4567 ≈ K4567 • X02
  proved = GL.•-cancelʳ {g = X02 • K4567} {g' = K4567 • X02} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01067.proved (MV01068.proved))) (trans (cong refl R091.proved) (move-product MV01068.proved (MV01067.proved))))

module r2c_ij031245 where

  proved : X03 • K1245 ≈ K1245 • X03
  proved = GL.•-cancelʳ {g = X03 • K1245} {g' = K1245 • X03} {h = p (s0 • s1 • s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01069.proved (MV00679.proved))) (trans (cong refl R091.proved) (move-product MV00679.proved (MV01069.proved))))

module r2c_ij031246 where

  proved : X03 • K1246 ≈ K1246 • X03
  proved = GL.•-cancelʳ {g = X03 • K1246} {g' = K1246 • X03} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01070.proved (MV00680.proved))) (trans (cong refl R091.proved) (move-product MV00680.proved (MV01070.proved))))

module r2c_ij031247 where

  proved : X03 • K1247 ≈ K1247 • X03
  proved = GL.•-cancelʳ {g = X03 • K1247} {g' = K1247 • X03} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01071.proved (MV00681.proved))) (trans (cong refl R091.proved) (move-product MV00681.proved (MV01071.proved))))

module r2c_ij031256 where

  proved : X03 • K1256 ≈ K1256 • X03
  proved = GL.•-cancelʳ {g = X03 • K1256} {g' = K1256 • X03} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01072.proved (MV00682.proved))) (trans (cong refl R091.proved) (move-product MV00682.proved (MV01072.proved))))

module r2c_ij031257 where

  proved : X03 • K1257 ≈ K1257 • X03
  proved = GL.•-cancelʳ {g = X03 • K1257} {g' = K1257 • X03} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01073.proved (MV00683.proved))) (trans (cong refl R091.proved) (move-product MV00683.proved (MV01073.proved))))

module r2c_ij031267 where

  proved : X03 • K1267 ≈ K1267 • X03
  proved = GL.•-cancelʳ {g = X03 • K1267} {g' = K1267 • X03} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01074.proved (MV00684.proved))) (trans (cong refl R091.proved) (move-product MV00684.proved (MV01074.proved))))

module r2c_ij031456 where

  proved : X03 • K1456 ≈ K1456 • X03
  proved = GL.•-cancelʳ {g = X03 • K1456} {g' = K1456 • X03} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01075.proved (MV01076.proved))) (trans (cong refl R091.proved) (move-product MV01076.proved (MV01075.proved))))

module r2c_ij031457 where

  proved : X03 • K1457 ≈ K1457 • X03
  proved = GL.•-cancelʳ {g = X03 • K1457} {g' = K1457 • X03} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01077.proved (MV01078.proved))) (trans (cong refl R091.proved) (move-product MV01078.proved (MV01077.proved))))

module r2c_ij031467 where

  proved : X03 • K1467 ≈ K1467 • X03
  proved = GL.•-cancelʳ {g = X03 • K1467} {g' = K1467 • X03} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01079.proved (MV01080.proved))) (trans (cong refl R091.proved) (move-product MV01080.proved (MV01079.proved))))

module r2c_ij031567 where

  proved : X03 • K1567 ≈ K1567 • X03
  proved = GL.•-cancelʳ {g = X03 • K1567} {g' = K1567 • X03} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01081.proved (MV01082.proved))) (trans (cong refl R091.proved) (move-product MV01082.proved (MV01081.proved))))

module r2c_ij032456 where

  proved : X03 • K2456 ≈ K2456 • X03
  proved = GL.•-cancelʳ {g = X03 • K2456} {g' = K2456 • X03} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01083.proved (MV01084.proved))) (trans (cong refl R091.proved) (move-product MV01084.proved (MV01083.proved))))

module r2c_ij032457 where

  proved : X03 • K2457 ≈ K2457 • X03
  proved = GL.•-cancelʳ {g = X03 • K2457} {g' = K2457 • X03} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01085.proved (MV01086.proved))) (trans (cong refl R091.proved) (move-product MV01086.proved (MV01085.proved))))

module r2c_ij032467 where

  proved : X03 • K2467 ≈ K2467 • X03
  proved = GL.•-cancelʳ {g = X03 • K2467} {g' = K2467 • X03} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01087.proved (MV01088.proved))) (trans (cong refl R091.proved) (move-product MV01088.proved (MV01087.proved))))

module r2c_ij032567 where

  proved : X03 • K2567 ≈ K2567 • X03
  proved = GL.•-cancelʳ {g = X03 • K2567} {g' = K2567 • X03} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01089.proved (MV01090.proved))) (trans (cong refl R091.proved) (move-product MV01090.proved (MV01089.proved))))

module r2c_ij034567 where

  proved : X03 • K4567 ≈ K4567 • X03
  proved = GL.•-cancelʳ {g = X03 • K4567} {g' = K4567 • X03} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01091.proved (MV01092.proved))) (trans (cong refl R091.proved) (move-product MV01092.proved (MV01091.proved))))

module r2c_ij041235 where

  proved : X04 • K1235 ≈ K1235 • X04
  proved = GL.•-cancelʳ {g = X04 • K1235} {g' = K1235 • X04} {h = p (s0 • s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV01093.proved (MV00676.proved))) (trans (cong refl R091.proved) (move-product MV00676.proved (MV01093.proved))))

module r2c_ij041236 where

  proved : X04 • K1236 ≈ K1236 • X04
  proved = GL.•-cancelʳ {g = X04 • K1236} {g' = K1236 • X04} {h = p (s0 • s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01094.proved (MV00677.proved))) (trans (cong refl R091.proved) (move-product MV00677.proved (MV01094.proved))))

module r2c_ij041237 where

  proved : X04 • K1237 ≈ K1237 • X04
  proved = GL.•-cancelʳ {g = X04 • K1237} {g' = K1237 • X04} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01095.proved (MV00678.proved))) (trans (cong refl R091.proved) (move-product MV00678.proved (MV01095.proved))))

module r2c_ij041256 where

  proved : X04 • K1256 ≈ K1256 • X04
  proved = GL.•-cancelʳ {g = X04 • K1256} {g' = K1256 • X04} {h = p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01096.proved (MV01097.proved))) (trans (cong refl R091.proved) (move-product MV01097.proved (MV01096.proved))))

module r2c_ij041257 where

  proved : X04 • K1257 ≈ K1257 • X04
  proved = GL.•-cancelʳ {g = X04 • K1257} {g' = K1257 • X04} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01098.proved (MV01099.proved))) (trans (cong refl R091.proved) (move-product MV01099.proved (MV01098.proved))))

module r2c_ij041267 where

  proved : X04 • K1267 ≈ K1267 • X04
  proved = GL.•-cancelʳ {g = X04 • K1267} {g' = K1267 • X04} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01100.proved (MV01101.proved))) (trans (cong refl R091.proved) (move-product MV01101.proved (MV01100.proved))))

module r2c_ij041356 where

  proved : X04 • K1356 ≈ K1356 • X04
  proved = GL.•-cancelʳ {g = X04 • K1356} {g' = K1356 • X04} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01102.proved (MV01103.proved))) (trans (cong refl R091.proved) (move-product MV01103.proved (MV01102.proved))))

module r2c_ij041357 where

  proved : X04 • K1357 ≈ K1357 • X04
  proved = GL.•-cancelʳ {g = X04 • K1357} {g' = K1357 • X04} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01104.proved (MV01105.proved))) (trans (cong refl R091.proved) (move-product MV01105.proved (MV01104.proved))))

module r2c_ij041367 where

  proved : X04 • K1367 ≈ K1367 • X04
  proved = GL.•-cancelʳ {g = X04 • K1367} {g' = K1367 • X04} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01106.proved (MV01107.proved))) (trans (cong refl R091.proved) (move-product MV01107.proved (MV01106.proved))))

module r2c_ij041567 where

  proved : X04 • K1567 ≈ K1567 • X04
  proved = GL.•-cancelʳ {g = X04 • K1567} {g' = K1567 • X04} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01108.proved (MV01109.proved))) (trans (cong refl R091.proved) (move-product MV01109.proved (MV01108.proved))))

module r2c_ij042356 where

  proved : X04 • K2356 ≈ K2356 • X04
  proved = GL.•-cancelʳ {g = X04 • K2356} {g' = K2356 • X04} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01110.proved (MV01111.proved))) (trans (cong refl R091.proved) (move-product MV01111.proved (MV01110.proved))))

module r2c_ij042357 where

  proved : X04 • K2357 ≈ K2357 • X04
  proved = GL.•-cancelʳ {g = X04 • K2357} {g' = K2357 • X04} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01112.proved (MV01113.proved))) (trans (cong refl R091.proved) (move-product MV01113.proved (MV01112.proved))))

module r2c_ij042367 where

  proved : X04 • K2367 ≈ K2367 • X04
  proved = GL.•-cancelʳ {g = X04 • K2367} {g' = K2367 • X04} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01114.proved (MV01115.proved))) (trans (cong refl R091.proved) (move-product MV01115.proved (MV01114.proved))))

module r2c_ij042567 where

  proved : X04 • K2567 ≈ K2567 • X04
  proved = GL.•-cancelʳ {g = X04 • K2567} {g' = K2567 • X04} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01116.proved (MV01117.proved))) (trans (cong refl R091.proved) (move-product MV01117.proved (MV01116.proved))))

module r2c_ij043567 where

  proved : X04 • K3567 ≈ K3567 • X04
  proved = GL.•-cancelʳ {g = X04 • K3567} {g' = K3567 • X04} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01118.proved (MV01119.proved))) (trans (cong refl R091.proved) (move-product MV01119.proved (MV01118.proved))))
