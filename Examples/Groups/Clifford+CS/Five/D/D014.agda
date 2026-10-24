{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD014 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D014 (Sᴰ : SD014) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-nat-SWbc-at0213243140 : Ws → St 447
  lem-nat-SWbc-at0213243140 = pickᴰ 0 Sᴰ
  lem-nat-SWbc-at03102132 : Ws → St 448
  lem-nat-SWbc-at03102132 = pickᴰ 1 Sᴰ
  lem-nat-SWbc-at032032 : Ws → St 449
  lem-nat-SWbc-at032032 = pickᴰ 2 Sᴰ
  lem-nat-SWbc-at04203243 : Ws → St 450
  lem-nat-SWbc-at04203243 = pickᴰ 3 Sᴰ
  lem-nat-SWbc-at13243142 : Ws → St 451
  lem-nat-SWbc-at13243142 = pickᴰ 4 Sᴰ
  lem-nat-SWbc-at13243241 : Ws → St 452
  lem-nat-SWbc-at13243241 = pickᴰ 5 Sᴰ
  lem-nat-SWbc-at14233142 : Ws → St 453
  lem-nat-SWbc-at14233142 = pickᴰ 6 Sᴰ
  lem-tP-at021021 : Ws → St 123
  lem-tP-at021021 = pickᴰ 7 Sᴰ
  lem-tP-at0210213443 : Ws → St 124
  lem-tP-at0210213443 = pickᴰ 8 Sᴰ
  lem-tP-at0213243140 : Ws → St 144
  lem-tP-at0213243140 = pickᴰ 9 Sᴰ
  lem-tP-at0220 : Ws → St 125
  lem-tP-at0220 = pickᴰ 10 Sᴰ
  lem-tP-at03102132 : Ws → St 126
  lem-tP-at03102132 = pickᴰ 11 Sᴰ
  lem-tP-at032032 : Ws → St 127
  lem-tP-at032032 = pickᴰ 12 Sᴰ
  lem-tP-at0410213243 : Ws → St 128
  lem-tP-at0410213243 = pickᴰ 13 Sᴰ
  lem-tP-at04203243 : Ws → St 129
  lem-tP-at04203243 = pickᴰ 14 Sᴰ
  lem-tP-at13243142 : Ws → St 130
  lem-tP-at13243142 = pickᴰ 15 Sᴰ
  lem-tP-at13243241 : Ws → St 131
  lem-tP-at13243241 = pickᴰ 16 Sᴰ
  lem-tP-at14233142 : Ws → St 132
  lem-tP-at14233142 = pickᴰ 17 Sᴰ
  lem-tP-at14233241 : Ws → St 133
  lem-tP-at14233241 = pickᴰ 18 Sᴰ
  lem-nat-SWbc-at0310213442 : Ws → St 454
  lem-nat-SWbc-at0310213442 = pickᴰ 19 Sᴰ
  lem-nat-SWbc-at14233241 : Ws → St 455
  lem-nat-SWbc-at14233241 = pickᴰ 20 Sᴰ
  lem-nat-SWbc-at0220 : Ws → St 456
  lem-nat-SWbc-at0220 = pickᴰ 21 Sᴰ
  lem-CSdu-box-1 : Ws → St 457
  lem-CSdu-box-1 = pickᴰ 22 Sᴰ
  lem-CSdu-box-2 : Ws → St 458
  lem-CSdu-box-2 = pickᴰ 23 Sᴰ
  lem-CSdu-box-2-at0210243143 : Ws → St 459
  lem-CSdu-box-2-at0210243143 = pickᴰ 24 Sᴰ
  lem-CSdu-box-2-at122441 : Ws → St 460
  lem-CSdu-box-2-at122441 = pickᴰ 25 Sᴰ
  lem-CSdu-box-2-at243243 : Ws → St 461
  lem-CSdu-box-2-at243243 = pickᴰ 26 Sᴰ
  lem-CSu-box-1 : Ws → St 462
  lem-CSu-box-1 = pickᴰ 27 Sᴰ
  lem-CSu-box-2 : Ws → St 463
  lem-CSu-box-2 = pickᴰ 28 Sᴰ
  lem-CSu-box-2-at122441 : Ws → St 464
  lem-CSu-box-2-at122441 = pickᴰ 29 Sᴰ
  lem-CSu-box-2-at243243 : Ws → St 465
  lem-CSu-box-2-at243243 = pickᴰ 30 Sᴰ
  lem-CXbc-box : Ws → St 466
  lem-CXbc-box = pickᴰ 31 Sᴰ
  lem-CXbc-box-at0214203143 : Ws → St 467
  lem-CXbc-box-at0214203143 = pickᴰ 32 Sᴰ
  lem-CXbc-box-at0330 : Ws → St 468
  lem-CXbc-box-at0330 = pickᴰ 33 Sᴰ
  lem-CXbc-box-at043043 : Ws → St 469
  lem-CXbc-box-at043043 = pickᴰ 34 Sᴰ
  lem-CXbc-box-at1221 : Ws → St 470
  lem-CXbc-box-at1221 = pickᴰ 35 Sᴰ
  lem-CXbc-box-at12243143 : Ws → St 471
  lem-CXbc-box-at12243143 = pickᴰ 36 Sᴰ
  lem-CXbc-box-at13213442 : Ws → St 472
  lem-CXbc-box-at13213442 = pickᴰ 37 Sᴰ
  lem-CXbc-box-at133441 : Ws → St 473
  lem-CXbc-box-at133441 = pickᴰ 38 Sᴰ
  lem-CXcb-box : Ws → St 474
  lem-CXcb-box = pickᴰ 39 Sᴰ
  lem-CXcb-box-at0214203143 : Ws → St 475
  lem-CXcb-box-at0214203143 = pickᴰ 40 Sᴰ
  lem-CXcb-box-at0330 : Ws → St 476
  lem-CXcb-box-at0330 = pickᴰ 41 Sᴰ
  lem-CXcb-box-at043043 : Ws → St 477
  lem-CXcb-box-at043043 = pickᴰ 42 Sᴰ
  lem-CXcb-box-at1221 : Ws → St 478
  lem-CXcb-box-at1221 = pickᴰ 43 Sᴰ
  lem-CXcb-box-at12243143 : Ws → St 479
  lem-CXcb-box-at12243143 = pickᴰ 44 Sᴰ
  lem-CXcb-box-at13213442 : Ws → St 480
  lem-CXcb-box-at13213442 = pickᴰ 45 Sᴰ
  lem-CXcb-box-at133441 : Ws → St 481
  lem-CXcb-box-at133441 = pickᴰ 46 Sᴰ
  lem-QVQ-at021021 : Ws → St 482
  lem-QVQ-at021021 = pickᴰ 47 Sᴰ
  lem-QVQ-at03102132 : Ws → St 483
  lem-QVQ-at03102132 = pickᴰ 48 Sᴰ
  lem-QVQ-at0410213243 : Ws → St 484
  lem-QVQ-at0410213243 = pickᴰ 49 Sᴰ
  lem-QVQ-at04203243 : Ws → St 485
  lem-QVQ-at04203243 = pickᴰ 50 Sᴰ
  lem-QVQ-at13243142 : Ws → St 486
  lem-QVQ-at13243142 = pickᴰ 51 Sᴰ
  lem-QVQ-at13243241 : Ws → St 487
  lem-QVQ-at13243241 = pickᴰ 52 Sᴰ
  lem-QVQ-at14233142 : Ws → St 488
  lem-QVQ-at14233142 = pickᴰ 53 Sᴰ
  lem-SWbc-box-at032032 : Ws → St 489
  lem-SWbc-box-at032032 = pickᴰ 54 Sᴰ
  lem-SWbc-box-at04203243 : Ws → St 490
  lem-SWbc-box-at04203243 = pickᴰ 55 Sᴰ
  lem-SWbc-box-at13243142 : Ws → St 491
  lem-SWbc-box-at13243142 = pickᴰ 56 Sᴰ
  lem-SWbc-box-at13243241 : Ws → St 492
  lem-SWbc-box-at13243241 = pickᴰ 57 Sᴰ
  lem-SWbc-box-at14233142 : Ws → St 493
  lem-SWbc-box-at14233142 = pickᴰ 58 Sᴰ
  lem-Sdu-box : Ws → St 494
  lem-Sdu-box = pickᴰ 59 Sᴰ
  lem-Su-box : Ws → St 495
  lem-Su-box = pickᴰ 60 Sᴰ
  lem-Su-box-at0210243143 : Ws → St 496
  lem-Su-box-at0210243143 = pickᴰ 61 Sᴰ
  lem-Su-box-at122441 : Ws → St 497
  lem-Su-box-at122441 = pickᴰ 62 Sᴰ
  lem-Su-box-at243243 : Ws → St 498
  lem-Su-box-at243243 = pickᴰ 63 Sᴰ
  lem-VPQ : Ws → St 499
  lem-VPQ = pickᴰ 64 Sᴰ
  lem-VPQ-at0110 : Ws → St 500
  lem-VPQ-at0110 = pickᴰ 65 Sᴰ
  lem-VPQ-at0210243143 : Ws → St 501
  lem-VPQ-at0210243143 = pickᴰ 66 Sᴰ
  lem-VPQ-at0310243142 : Ws → St 502
  lem-VPQ-at0310243142 = pickᴰ 67 Sᴰ
  lem-VPQ-at0314203142 : Ws → St 503
  lem-VPQ-at0314203142 = pickᴰ 68 Sᴰ
  lem-VPQ-at0330 : Ws → St 504
  lem-VPQ-at0330 = pickᴰ 69 Sᴰ
  lem-VPQ-at043043 : Ws → St 505
  lem-VPQ-at043043 = pickᴰ 70 Sᴰ
  lem-VPQ-at1221 : Ws → St 506
  lem-VPQ-at1221 = pickᴰ 71 Sᴰ
  lem-VPQ-at122331 : Ws → St 507
  lem-VPQ-at122331 = pickᴰ 72 Sᴰ
  lem-VPQ-at122441 : Ws → St 508
  lem-VPQ-at122441 = pickᴰ 73 Sᴰ
  lem-VPQ-at132132 : Ws → St 509
  lem-VPQ-at132132 = pickᴰ 74 Sᴰ
  lem-VPQ-at13213442 : Ws → St 510
  lem-VPQ-at13213442 = pickᴰ 75 Sᴰ
  lem-VPQ-at1331 : Ws → St 511
  lem-VPQ-at1331 = pickᴰ 76 Sᴰ
  lem-VPQ-at2332 : Ws → St 512
  lem-VPQ-at2332 = pickᴰ 77 Sᴰ
  lem-VPQ-at243243 : Ws → St 513
  lem-VPQ-at243243 = pickᴰ 78 Sᴰ
  lem-VPQ-at3443 : Ws → St 514
  lem-VPQ-at3443 = pickᴰ 79 Sᴰ
  lem-CSu-box-2-at0210243143 : Ws → St 515
  lem-CSu-box-2-at0210243143 = pickᴰ 80 Sᴰ
  lem-CXbc-box-at0210243143 : Ws → St 516
  lem-CXbc-box-at0210243143 = pickᴰ 81 Sᴰ
  lem-CXbc-box-at0213213440 : Ws → St 517
  lem-CXbc-box-at0213213440 = pickᴰ 82 Sᴰ
  lem-CXbc-box-at0214213043 : Ws → St 518
  lem-CXbc-box-at0214213043 = pickᴰ 83 Sᴰ
  lem-CXbc-box-at022330 : Ws → St 519
  lem-CXbc-box-at022330 = pickᴰ 84 Sᴰ
  lem-CXbc-box-at02233440 : Ws → St 520
  lem-CXbc-box-at02233440 = pickᴰ 85 Sᴰ
  lem-CXbc-box-at022440 : Ws → St 521
  lem-CXbc-box-at022440 = pickᴰ 86 Sᴰ
  lem-CXbc-box-at0312213440 : Ws → St 522
  lem-CXbc-box-at0312213440 = pickᴰ 87 Sᴰ
  lem-CXbc-box-at0312243140 : Ws → St 523
  lem-CXbc-box-at0312243140 = pickᴰ 88 Sᴰ
  lem-CXbc-box-at0314203142 : Ws → St 524
  lem-CXbc-box-at0314203142 = pickᴰ 89 Sᴰ
  lem-CXbc-box-at0314213042 : Ws → St 525
  lem-CXbc-box-at0314213042 = pickᴰ 90 Sᴰ
  lem-CXbc-box-at122331 : Ws → St 526
  lem-CXbc-box-at122331 = pickᴰ 91 Sᴰ
  lem-CXbc-box-at12233441 : Ws → St 527
  lem-CXbc-box-at12233441 = pickᴰ 92 Sᴰ
  lem-CXbc-box-at122441 : Ws → St 528
  lem-CXbc-box-at122441 = pickᴰ 93 Sᴰ
  lem-CXbc-box-at132132 : Ws → St 529
  lem-CXbc-box-at132132 = pickᴰ 94 Sᴰ
  lem-CXbc-box-at1331 : Ws → St 530
  lem-CXbc-box-at1331 = pickᴰ 95 Sᴰ
  lem-CXbc-box-at14213243 : Ws → St 531
  lem-CXbc-box-at14213243 = pickᴰ 96 Sᴰ
  lem-CXbc-box-at1441 : Ws → St 532
  lem-CXbc-box-at1441 = pickᴰ 97 Sᴰ
  lem-CXbc-box-at2332 : Ws → St 533
  lem-CXbc-box-at2332 = pickᴰ 98 Sᴰ
  lem-CXbc-box-at243243 : Ws → St 534
  lem-CXbc-box-at243243 = pickᴰ 99 Sᴰ
  lem-CXcb-box-at0210243143 : Ws → St 535
  lem-CXcb-box-at0210243143 = pickᴰ 100 Sᴰ
  lem-CXcb-box-at0213213440 : Ws → St 536
  lem-CXcb-box-at0213213440 = pickᴰ 101 Sᴰ
  lem-CXcb-box-at0214213043 : Ws → St 537
  lem-CXcb-box-at0214213043 = pickᴰ 102 Sᴰ
  lem-CXcb-box-at022330 : Ws → St 538
  lem-CXcb-box-at022330 = pickᴰ 103 Sᴰ
  lem-CXcb-box-at02233440 : Ws → St 539
  lem-CXcb-box-at02233440 = pickᴰ 104 Sᴰ
  lem-CXcb-box-at0312213440 : Ws → St 540
  lem-CXcb-box-at0312213440 = pickᴰ 105 Sᴰ
  lem-CXcb-box-at0312243140 : Ws → St 541
  lem-CXcb-box-at0312243140 = pickᴰ 106 Sᴰ
  lem-CXcb-box-at0314203142 : Ws → St 542
  lem-CXcb-box-at0314203142 = pickᴰ 107 Sᴰ
  lem-CXcb-box-at0314213042 : Ws → St 543
  lem-CXcb-box-at0314213042 = pickᴰ 108 Sᴰ
  lem-CXcb-box-at122331 : Ws → St 544
  lem-CXcb-box-at122331 = pickᴰ 109 Sᴰ
  lem-CXcb-box-at12233441 : Ws → St 545
  lem-CXcb-box-at12233441 = pickᴰ 110 Sᴰ
  lem-CXcb-box-at122441 : Ws → St 546
  lem-CXcb-box-at122441 = pickᴰ 111 Sᴰ
  lem-CXcb-box-at132132 : Ws → St 547
  lem-CXcb-box-at132132 = pickᴰ 112 Sᴰ
  lem-CXcb-box-at1331 : Ws → St 548
  lem-CXcb-box-at1331 = pickᴰ 113 Sᴰ
  lem-CXcb-box-at14213243 : Ws → St 549
  lem-CXcb-box-at14213243 = pickᴰ 114 Sᴰ
  lem-CXcb-box-at1441 : Ws → St 550
  lem-CXcb-box-at1441 = pickᴰ 115 Sᴰ
  lem-CXcb-box-at2332 : Ws → St 551
  lem-CXcb-box-at2332 = pickᴰ 116 Sᴰ
  lem-CXcb-box-at243243 : Ws → St 552
  lem-CXcb-box-at243243 = pickᴰ 117 Sᴰ
  lem-QVQ-at0210213443 : Ws → St 553
  lem-QVQ-at0210213443 = pickᴰ 118 Sᴰ
  lem-QVQ-at0213243140 : Ws → St 554
  lem-QVQ-at0213243140 = pickᴰ 119 Sᴰ
  lem-QVQ-at0220 : Ws → St 555
  lem-QVQ-at0220 = pickᴰ 120 Sᴰ
  lem-QVQ-at032032 : Ws → St 556
  lem-QVQ-at032032 = pickᴰ 121 Sᴰ
  lem-QVQ-at14233241 : Ws → St 557
  lem-QVQ-at14233241 = pickᴰ 122 Sᴰ
  lem-SWbc-box-at0213243140 : Ws → St 558
  lem-SWbc-box-at0213243140 = pickᴰ 123 Sᴰ
  lem-SWbc-box-at0220 : Ws → St 559
  lem-SWbc-box-at0220 = pickᴰ 124 Sᴰ
  lem-SWbc-box-at03102132 : Ws → St 560
  lem-SWbc-box-at03102132 = pickᴰ 125 Sᴰ
  lem-VPQ-at0210233441 : Ws → St 561
  lem-VPQ-at0210233441 = pickᴰ 126 Sᴰ
  lem-VPQ-at0213203441 : Ws → St 562
  lem-VPQ-at0213203441 = pickᴰ 127 Sᴰ
  lem-VPQ-at0214203143 : Ws → St 563
  lem-VPQ-at0214203143 = pickᴰ 128 Sᴰ
  lem-VPQ-at0214213043 : Ws → St 564
  lem-VPQ-at0214213043 = pickᴰ 129 Sᴰ
  lem-VPQ-at022330 : Ws → St 565
  lem-VPQ-at022330 = pickᴰ 130 Sᴰ
  lem-VPQ-at022440 : Ws → St 566
  lem-VPQ-at022440 = pickᴰ 131 Sᴰ
  lem-VPQ-at0312243140 : Ws → St 567
  lem-VPQ-at0312243140 = pickᴰ 132 Sᴰ
  lem-VPQ-at0314213042 : Ws → St 568
  lem-VPQ-at0314213042 = pickᴰ 133 Sᴰ
  lem-VPQ-at12213443 : Ws → St 569
  lem-VPQ-at12213443 = pickᴰ 134 Sᴰ
  lem-VPQ-at12233441 : Ws → St 570
  lem-VPQ-at12233441 = pickᴰ 135 Sᴰ
  lem-VPQ-at14213243 : Ws → St 571
  lem-VPQ-at14213243 = pickᴰ 136 Sᴰ
  lem-VPQ-at143143 : Ws → St 572
  lem-VPQ-at143143 = pickᴰ 137 Sᴰ
  lem-VPQ-at233442 : Ws → St 573
  lem-VPQ-at233442 = pickᴰ 138 Sᴰ
  lem-CXbc-box-at0210233441 : Ws → St 574
  lem-CXbc-box-at0210233441 = pickᴰ 139 Sᴰ
  lem-CXbc-box-at02102441 : Ws → St 575
  lem-CXbc-box-at02102441 = pickᴰ 140 Sᴰ
  lem-CXbc-box-at02142041 : Ws → St 576
  lem-CXbc-box-at02142041 = pickᴰ 141 Sᴰ
  lem-CXbc-box-at0310243142 : Ws → St 577
  lem-CXbc-box-at0310243142 = pickᴰ 142 Sᴰ
  lem-CXbc-box-at0310243241 : Ws → St 578
  lem-CXbc-box-at0310243241 = pickᴰ 143 Sᴰ
  lem-CXbc-box-at031031 : Ws → St 579
  lem-CXbc-box-at031031 = pickᴰ 144 Sᴰ
  lem-CXbc-box-at03103441 : Ws → St 580
  lem-CXbc-box-at03103441 = pickᴰ 145 Sᴰ
  lem-CXbc-box-at0312203441 : Ws → St 581
  lem-CXbc-box-at0312203441 = pickᴰ 146 Sᴰ
  lem-CXbc-box-at0312243041 : Ws → St 582
  lem-CXbc-box-at0312243041 = pickᴰ 147 Sᴰ
  lem-CXbc-box-at0314213240 : Ws → St 583
  lem-CXbc-box-at0314213240 = pickᴰ 148 Sᴰ
  lem-CXbc-box-at03143041 : Ws → St 584
  lem-CXbc-box-at03143041 = pickᴰ 149 Sᴰ
  lem-CXbc-box-at03143140 : Ws → St 585
  lem-CXbc-box-at03143140 = pickᴰ 150 Sᴰ
  lem-CXbc-box-at03243240 : Ws → St 586
  lem-CXbc-box-at03243240 = pickᴰ 151 Sᴰ
  lem-CXbc-box-at033440 : Ws → St 587
  lem-CXbc-box-at033440 = pickᴰ 152 Sᴰ
  lem-CXbc-box-at12213443 : Ws → St 588
  lem-CXbc-box-at12213443 = pickᴰ 153 Sᴰ
  lem-CXbc-box-at143143 : Ws → St 589
  lem-CXbc-box-at143143 = pickᴰ 154 Sᴰ
  lem-CXbc-box-at233442 : Ws → St 590
  lem-CXbc-box-at233442 = pickᴰ 155 Sᴰ
  lem-CXbc-box-at2442 : Ws → St 591
  lem-CXbc-box-at2442 = pickᴰ 156 Sᴰ
  lem-CXbc-box-at3443 : Ws → St 592
  lem-CXbc-box-at3443 = pickᴰ 157 Sᴰ
  lem-CXcb-box-at0210233441 : Ws → St 593
  lem-CXcb-box-at0210233441 = pickᴰ 158 Sᴰ
  lem-CXcb-box-at02102441 : Ws → St 594
  lem-CXcb-box-at02102441 = pickᴰ 159 Sᴰ
  lem-CXcb-box-at022440 : Ws → St 595
  lem-CXcb-box-at022440 = pickᴰ 160 Sᴰ
  lem-CXcb-box-at0310243142 : Ws → St 596
  lem-CXcb-box-at0310243142 = pickᴰ 161 Sᴰ
  lem-CXcb-box-at0310243241 : Ws → St 597
  lem-CXcb-box-at0310243241 = pickᴰ 162 Sᴰ
  lem-CXcb-box-at031031 : Ws → St 598
  lem-CXcb-box-at031031 = pickᴰ 163 Sᴰ
  lem-CXcb-box-at03103441 : Ws → St 599
  lem-CXcb-box-at03103441 = pickᴰ 164 Sᴰ
  lem-CXcb-box-at0312203441 : Ws → St 600
  lem-CXcb-box-at0312203441 = pickᴰ 165 Sᴰ
  lem-CXcb-box-at0312243041 : Ws → St 601
  lem-CXcb-box-at0312243041 = pickᴰ 166 Sᴰ
  lem-CXcb-box-at0314213240 : Ws → St 602
  lem-CXcb-box-at0314213240 = pickᴰ 167 Sᴰ
  lem-CXcb-box-at03143041 : Ws → St 603
  lem-CXcb-box-at03143041 = pickᴰ 168 Sᴰ
  lem-CXcb-box-at03143140 : Ws → St 604
  lem-CXcb-box-at03143140 = pickᴰ 169 Sᴰ
  lem-CXcb-box-at03243240 : Ws → St 605
  lem-CXcb-box-at03243240 = pickᴰ 170 Sᴰ
  lem-CXcb-box-at033440 : Ws → St 606
  lem-CXcb-box-at033440 = pickᴰ 171 Sᴰ
  lem-CXcb-box-at12213443 : Ws → St 607
  lem-CXcb-box-at12213443 = pickᴰ 172 Sᴰ
  lem-CXcb-box-at143143 : Ws → St 608
  lem-CXcb-box-at143143 = pickᴰ 173 Sᴰ
  lem-CXcb-box-at233442 : Ws → St 609
  lem-CXcb-box-at233442 = pickᴰ 174 Sᴰ
  lem-CXcb-box-at2442 : Ws → St 610
  lem-CXcb-box-at2442 = pickᴰ 175 Sᴰ
  lem-CXcb-box-at3443 : Ws → St 611
  lem-CXcb-box-at3443 = pickᴰ 176 Sᴰ
  lem-SWbc-box-at0310213442 : Ws → St 612
  lem-SWbc-box-at0310213442 = pickᴰ 177 Sᴰ
  lem-SWbc-box-at14233241 : Ws → St 613
  lem-SWbc-box-at14233241 = pickᴰ 178 Sᴰ
  lem-VPQ-at02102441 : Ws → St 614
  lem-VPQ-at02102441 = pickᴰ 179 Sᴰ
  lem-VPQ-at02233440 : Ws → St 615
  lem-VPQ-at02233440 = pickᴰ 180 Sᴰ
  lem-VPQ-at0310243241 : Ws → St 616
  lem-VPQ-at0310243241 = pickᴰ 181 Sᴰ
  lem-VPQ-at031031 : Ws → St 617
  lem-VPQ-at031031 = pickᴰ 182 Sᴰ
  lem-VPQ-at03103441 : Ws → St 618
  lem-VPQ-at03103441 = pickᴰ 183 Sᴰ
  lem-VPQ-at0312203441 : Ws → St 619
  lem-VPQ-at0312203441 = pickᴰ 184 Sᴰ
  lem-VPQ-at0312243041 : Ws → St 620
  lem-VPQ-at0312243041 = pickᴰ 185 Sᴰ
  lem-VPQ-at0314213240 : Ws → St 621
  lem-VPQ-at0314213240 = pickᴰ 186 Sᴰ
  lem-VPQ-at03143140 : Ws → St 622
  lem-VPQ-at03143140 = pickᴰ 187 Sᴰ
  lem-VPQ-at03243240 : Ws → St 623
  lem-VPQ-at03243240 = pickᴰ 188 Sᴰ
  lem-VPQ-at033440 : Ws → St 624
  lem-VPQ-at033440 = pickᴰ 189 Sᴰ
  lem-VPQ-at12243143 : Ws → St 625
  lem-VPQ-at12243143 = pickᴰ 190 Sᴰ
  lem-VPQ-at1441 : Ws → St 626
  lem-VPQ-at1441 = pickᴰ 191 Sᴰ
  lem-VPQ-at2442 : Ws → St 627
  lem-VPQ-at2442 = pickᴰ 192 Sᴰ
  lem-CXcb-box-at02142041 : Ws → St 628
  lem-CXcb-box-at02142041 = pickᴰ 193 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wpE 6 c4
  q2 : Ws → Eqn
  q2 c4 = sE 499 (lem-VPQ c4)
  q3 : Ws → Eqn
  q3 c4 = wpE 7 c4

-- QVQ: 3 steps
lem-QVQ : Ws → ⟪ (ℓ "亠亍二亠") ⟫ʷ ≈ ⟪ (ℓ "亡亍二亡") ⟫ʷ
lem-QVQ c4 = derive (ℓ "亠亍二亠") (ℓ "亡亍二亡")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = wlE 180 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 501 (lem-VPQ-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 181 (lit c4)

-- QVQ @0210243143: 3 steps
lem-QVQ-at0210243143 : Ws → ⟪ (ℓ "交亞亜交") ⟫ʷ ≈ ⟪ (ℓ "亦亞亜亦") ⟫ʷ
lem-QVQ-at0210243143 c4 = derive (ℓ "交亞亜交") (ℓ "亦亞亜亦")
  (rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wlE 203 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 513 (lem-VPQ-at243243 c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 204 (lit c4)

-- QVQ @243243: 3 steps
lem-QVQ-at243243 : Ws → ⟪ (ℓ "亘井五亘") ⟫ʷ ≈ ⟪ (ℓ "亙井五亙") ⟫ʷ
lem-QVQ-at243243 c4 = derive (ℓ "亘井五亘") (ℓ "亙井五亙")
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q8 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = wlE 229 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 508 (lem-VPQ-at122441 c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 230 (lit c4)

-- QVQ @122441: 3 steps
lem-QVQ-at122441 : Ws → ⟪ (ℓ "亐亝亜亐") ⟫ʷ ≈ ⟪ (ℓ "云亝亜云") ⟫ʷ
lem-QVQ-at122441 c4 = derive (ℓ "亐亝亜亐") (ℓ "云亝亜云")
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = wlE 258 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 466 (lem-CXbc-box c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 259 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 474 (lem-CXcb-box c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 260 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = wlE 261 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 262 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 263 (lit c4)

-- SWbc-box: 11 steps
lem-SWbc-box : Ws → ⟪ (ℓ "乥亹乥") ⟫ʷ ≈ ⟪ (ℓ "亹") ⟫ʷ
lem-SWbc-box c4 = derive (ℓ "乥亹乥") (ℓ "亹")
  (rw⁻ 0 (q13 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wlE 278 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 470 (lem-CXbc-box-at1221 c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 279 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = sE 478 (lem-CXcb-box-at1221 c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 280 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 281 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 282 (lit c4)

-- SWbc-box @1221: 11 steps
lem-SWbc-box-at1221 : Ws → ⟪ (ℓ "乑仌乑") ⟫ʷ ≈ ⟪ (ℓ "仌") ⟫ʷ
lem-SWbc-box-at1221 c4 = derive (ℓ "乑仌乑") (ℓ "仌")
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q23 c4) ∷
   rw 1 (q24 c4) ∷
   rw 4 (q25 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = sE 506 (lem-VPQ-at1221 c4)

-- QVQ @1221: 3 steps
lem-QVQ-at1221 : Ws → ⟪ (ℓ "亠亍二亠") ⟫ʷ ≈ ⟪ (ℓ "亡亍二亡") ⟫ʷ
lem-QVQ-at1221 c4 = derive (ℓ "亠亍二亠") (ℓ "亡亍二亡")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wpE 80 c4
  q30 : Ws → Eqn
  q30 c4 = sE 512 (lem-VPQ-at2332 c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 135 c4

-- QVQ @2332: 3 steps
lem-QVQ-at2332 : Ws → ⟪ (ℓ "亜云亐亜") ⟫ʷ ≈ ⟪ (ℓ "亝云亐亝") ⟫ʷ
lem-QVQ-at2332 c4 = derive (ℓ "亜云亐亜") (ℓ "亝云亐亝")
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = sE 491 (lem-SWbc-box-at13243142 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 451 (lem-nat-SWbc-at13243142 c4)

-- sym-bc @13243142: 2 steps
lem-sym-bc-at13243142 : Ws → ⟪ (ℓ "仳") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-sym-bc-at13243142 c4 = derive (ℓ "仳") (ℓ "仩")
  (rw⁻ 0 (q32 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = wpE 51 c4
  q35 : Ws → Eqn
  q35 c4 = sE 507 (lem-VPQ-at122331 c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 161 c4

-- QVQ @122331: 3 steps
lem-QVQ-at122331 : Ws → ⟪ (ℓ "五亙亘五") ⟫ʷ ≈ ⟪ (ℓ "井亙亘井") ⟫ʷ
lem-QVQ-at122331 c4 = derive (ℓ "五亙亘五") (ℓ "井亙亘井")
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw 4 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = sE 492 (lem-SWbc-box-at13243241 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 452 (lem-nat-SWbc-at13243241 c4)

-- sym-bc @13243241: 2 steps
lem-sym-bc-at13243241 : Ws → ⟪ (ℓ "件") ⟫ʷ ≈ ⟪ (ℓ "仰") ⟫ʷ
lem-sym-bc-at13243241 c4 = derive (ℓ "件") (ℓ "仰")
  (rw⁻ 0 (q37 c4) ∷
   rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = sE 509 (lem-VPQ-at132132 c4)

-- QVQ @132132: 3 steps
lem-QVQ-at132132 : Ws → ⟪ (ℓ "亜云亐亜") ⟫ʷ ≈ ⟪ (ℓ "亝云亐亝") ⟫ʷ
lem-QVQ-at132132 c4 = derive (ℓ "亜云亐亜") (ℓ "亝云亐亝")
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = wlE 300 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = sE 471 (lem-CXbc-box-at12243143 c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 301 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = sE 479 (lem-CXcb-box-at12243143 c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 302 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 303 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 304 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 305 (lit c4)

-- SWbc-box @12243143: 11 steps
lem-SWbc-box-at12243143 : Ws → ⟪ (ℓ "乘仛乘") ⟫ʷ ≈ ⟪ (ℓ "仛") ⟫ʷ
lem-SWbc-box-at12243143 c4 = derive (ℓ "乘仛乘") (ℓ "仛")
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw 3 (q45 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = sE 493 (lem-SWbc-box-at14233142 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 453 (lem-nat-SWbc-at14233142 c4)

-- sym-bc @14233142: 2 steps
lem-sym-bc-at14233142 : Ws → ⟪ (ℓ "伋") ⟫ʷ ≈ ⟪ (ℓ "企") ⟫ʷ
lem-sym-bc-at14233142 c4 = derive (ℓ "伋") (ℓ "企")
  (rw⁻ 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = wpE 136 c4
  q51 : Ws → Eqn
  q51 c4 = sE 488 (lem-QVQ-at14233142 c4)
  q52 : Ws → Eqn
  q52 c4 = sE 132 (lem-tP-at14233142 c4)

-- box-cP @14233142: 12 steps
lem-box-cP-at14233142 : Ws → ⟪ (ℓ "伋") ⟫ʷ ≈ ⟪ (ℓ "亠亍亠亍") ⟫ʷ
lem-box-cP-at14233142 c4 = derive (ℓ "伋") (ℓ "亠亍亠亍")
  (re 0 1 (ℓ "亠亡伊亡亠伊") ∷
   re 2 1 (ℓ "五亗仿亗五仿") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q50 c4) ∷
   re 5 1 (ℓ "五亗仿亗五仿") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw⁻ 5 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = sE 510 (lem-VPQ-at13213442 c4)

-- QVQ @13213442: 3 steps
lem-QVQ-at13213442 : Ws → ⟪ (ℓ "亜云亐亜") ⟫ʷ ≈ ⟪ (ℓ "亝云亐亝") ⟫ʷ
lem-QVQ-at13213442 c4 = derive (ℓ "亜云亐亜") (ℓ "亝云亐亝")
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = sE 511 (lem-VPQ-at1331 c4)

-- QVQ @1331: 3 steps
lem-QVQ-at1331 : Ws → ⟪ (ℓ "五亙亘五") ⟫ʷ ≈ ⟪ (ℓ "井亙亘井") ⟫ʷ
lem-QVQ-at1331 c4 = derive (ℓ "五亙亘五") (ℓ "井亙亘井")
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 4 (q36 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wlE 364 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = sE 457 (lem-CSdu-box-1 c4)
  q57 : Ws → Eqn
  q57 c4 = sE 495 (lem-Su-box c4)

-- XCSX-box-1: 4 steps
lem-XCSX-box-1 : Ws → ⟪ (ℓ "且丨且亹") ⟫ʷ ≈ ⟪ (ℓ "亹且丨且") ⟫ʷ
lem-XCSX-box-1 c4 = derive (ℓ "且丨且亹") (ℓ "亹且丨且")
  (rw⁻ 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q55 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = wlE 365 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = sE 462 (lem-CSu-box-1 c4)
  q60 : Ws → Eqn
  q60 c4 = sE 494 (lem-Sdu-box c4)

-- XCSdX-box-1: 4 steps
lem-XCSdX-box-1 : Ws → ⟪ (ℓ "且丩且亹") ⟫ʷ ≈ ⟪ (ℓ "亹且丩且") ⟫ʷ
lem-XCSdX-box-1 c4 = derive (ℓ "且丩且亹") (ℓ "亹且丩且")
  (rw⁻ 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q58 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 377 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = sE 458 (lem-CSdu-box-2 c4)

-- XCSX-box-2: 4 steps
lem-XCSX-box-2 : Ws → ⟪ (ℓ "业丯业亹") ⟫ʷ ≈ ⟪ (ℓ "亹业丯业") ⟫ʷ
lem-XCSX-box-2 c4 = derive (ℓ "业丯业亹") (ℓ "亹业丯业")
  (rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q61 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = wlE 378 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = sE 463 (lem-CSu-box-2 c4)

-- XCSdX-box-2: 4 steps
lem-XCSdX-box-2 : Ws → ⟪ (ℓ "业丰业亹") ⟫ʷ ≈ ⟪ (ℓ "亹业丰业") ⟫ʷ
lem-XCSdX-box-2 c4 = derive (ℓ "业丰业亹") (ℓ "亹业丰业")
  (rw⁻ 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 0 (q60 c4) ∷
   rw 1 (q63 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 402 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = sE 500 (lem-VPQ-at0110 c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 321 (lit c4)

-- QVQ @0110: 3 steps
lem-QVQ-at0110 : Ws → ⟪ (ℓ "京于二京") ⟫ʷ ≈ ⟪ (ℓ "亭于二亭") ⟫ʷ
lem-QVQ-at0110 c4 = derive (ℓ "京于二京") (ℓ "亭于二亭")
  (rw⁻ 0 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wlE 405 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = sE 473 (lem-CXbc-box-at133441 c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 319 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = sE 481 (lem-CXcb-box-at133441 c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 406 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 317 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wlE 407 (lit c4)

-- SWbc-box @133441: 11 steps
lem-SWbc-box-at133441 : Ws → ⟪ (ℓ "乬仰乬") ⟫ʷ ≈ ⟪ (ℓ "仰") ⟫ʷ
lem-SWbc-box-at133441 c4 = derive (ℓ "乬仰乬") (ℓ "仰")
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q75 : Ws → Eqn
  q75 c4 = wlE 288 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = sE 487 (lem-QVQ-at13243241 c4)
  q77 : Ws → Eqn
  q77 c4 = sE 131 (lem-tP-at13243241 c4)

-- box-cP @13243241: 12 steps
lem-box-cP-at13243241 : Ws → ⟪ (ℓ "件") ⟫ʷ ≈ ⟪ (ℓ "亠亍亠亍") ⟫ʷ
lem-box-cP-at13243241 c4 = derive (ℓ "件") (ℓ "亠亍亠亍")
  (re 0 1 (ℓ "亠亡仵亡亠仵") ∷
   re 2 1 (ℓ "亘些仟些亘仟") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q75 c4) ∷
   re 5 1 (ℓ "亘些仟些亘仟") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = wpE 280 c4
  q79 : Ws → Eqn
  q79 c4 = sE 482 (lem-QVQ-at021021 c4)
  q80 : Ws → Eqn
  q80 c4 = sE 123 (lem-tP-at021021 c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 421 (lit c4)

-- box-cP @021021: 12 steps
lem-box-cP-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "二亱二亱") ⟫ʷ
lem-box-cP-at021021 c4 = derive (ℓ "伭") (ℓ "二亱二亱")
  (re 0 1 (ℓ "二亏他亏二他") ∷
   re 2 1 (ℓ "亘亙仍亙亘仍") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q78 c4) ∷
   re 5 1 (ℓ "亘亙仍亙亘仍") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = wlE 423 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = sE 472 (lem-CXbc-box-at13213442 c4)
  q84 : Ws → Eqn
  q84 c4 = sE 480 (lem-CXcb-box-at13213442 c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 424 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 425 (lit c4)

-- SWbc-box @13213442: 11 steps
lem-SWbc-box-at13213442 : Ws → ⟪ (ℓ "乘仩乘") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-SWbc-box-at13213442 c4 = derive (ℓ "乘仩乘") (ℓ "仩")
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 3 (q45 c4) ∷
   rw 1 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw 3 (q42 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q86 c4) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = wlE 269 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = sE 486 (lem-QVQ-at13243142 c4)
  q89 : Ws → Eqn
  q89 c4 = sE 130 (lem-tP-at13243142 c4)

-- box-cP @13243142: 12 steps
lem-box-cP-at13243142 : Ws → ⟪ (ℓ "仳") ⟫ʷ ≈ ⟪ (ℓ "亠亍亠亍") ⟫ʷ
lem-box-cP-at13243142 c4 = derive (ℓ "仳") (ℓ "亠亍亠亍")
  (re 0 1 (ℓ "亠亡仲亡亠仲") ∷
   re 2 1 (ℓ "亐亓仧亓亐仧") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q87 c4) ∷
   re 5 1 (ℓ "亐亓仧亓亐仧") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = sE 483 (lem-QVQ-at03102132 c4)
  q91 : Ws → Eqn
  q91 c4 = sE 126 (lem-tP-at03102132 c4)
  q92 : Ws → Eqn
  q92 c4 = wlE 443 (lit c4)

-- box-cP @03102132: 12 steps
lem-box-cP-at03102132 : Ws → ⟪ (ℓ "佤") ⟫ʷ ≈ ⟪ (ℓ "亐亲亐亲") ⟫ʷ
lem-box-cP-at03102132 c4 = derive (ℓ "佤") (ℓ "亐亲亐亲")
  (re 0 1 (ℓ "亐亓仮亓亐仮") ∷
   re 2 1 (ℓ "亘亙以亙亘以") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q78 c4) ∷
   re 5 1 (ℓ "亘亙以亙亘以") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q78 c4) ∷
   rw 2 (q90 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = sE 514 (lem-VPQ-at3443 c4)

-- QVQ @3443: 3 steps
lem-QVQ-at3443 : Ws → ⟪ (ℓ "亠亍二亠") ⟫ʷ ≈ ⟪ (ℓ "亡亍二亡") ⟫ʷ
lem-QVQ-at3443 c4 = derive (ℓ "亠亍二亠") (ℓ "亡亍二亡")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = wpE 305 c4
  q95 : Ws → Eqn
  q95 c4 = sE 484 (lem-QVQ-at0410213243 c4)
  q96 : Ws → Eqn
  q96 c4 = sE 128 (lem-tP-at0410213243 c4)
  q97 : Ws → Eqn
  q97 c4 = wpE 306 c4

-- box-cP @0410213243: 12 steps
lem-box-cP-at0410213243 : Ws → ⟪ (ℓ "侍") ⟫ʷ ≈ ⟪ (ℓ "五亳五亳") ⟫ʷ
lem-box-cP-at0410213243 c4 = derive (ℓ "侍") (ℓ "五亳五亳")
  (re 0 1 (ℓ "五亗伆亗五伆") ∷
   re 2 1 (ℓ "亜亝份亝亜份") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q94 c4) ∷
   re 5 1 (ℓ "亜亝份亝亜份") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q94 c4) ∷
   rw 2 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = wpE 317 c4
  q99 : Ws → Eqn
  q99 c4 = sE 505 (lem-VPQ-at043043 c4)

-- QVQ @043043: 3 steps
lem-QVQ-at043043 : Ws → ⟪ (ℓ "亠享亨亠") ⟫ʷ ≈ ⟪ (ℓ "亣享亨亣") ⟫ʷ
lem-QVQ-at043043 c4 = derive (ℓ "亠享亨亠") (ℓ "亣享亨亣")
  (rw⁻ 0 (q98 c4) ∷
   rw⁻ 1 (q99 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = wlE 480 (lit c4)
  q101 : Ws → Eqn
  q101 c4 = sE 469 (lem-CXbc-box-at043043 c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 481 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = sE 477 (lem-CXcb-box-at043043 c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 482 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 483 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 484 (lit c4)

-- SWbc-box @043043: 11 steps
lem-SWbc-box-at043043 : Ws → ⟪ (ℓ "串侓串") ⟫ʷ ≈ ⟪ (ℓ "侓") ⟫ʷ
lem-SWbc-box-at043043 c4 = derive (ℓ "串侓串") (ℓ "侓")
  (rw⁻ 0 (q100 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 4 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q106 c4) ∷
   rw 0 (q101 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = wlE 486 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = sE 485 (lem-QVQ-at04203243 c4)
  q109 : Ws → Eqn
  q109 c4 = sE 129 (lem-tP-at04203243 c4)

-- box-cP @04203243: 12 steps
lem-box-cP-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "五亳五亳") ⟫ʷ
lem-box-cP-at04203243 c4 = derive (ℓ "侒") (ℓ "五亳五亳")
  (re 0 1 (ℓ "五亗伫亗五伫") ∷
   re 2 1 (ℓ "亨亩伤亩亨伤") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw 2 (q107 c4) ∷
   re 5 1 (ℓ "亨亩伤亩亨伤") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw 5 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q97 c4) ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = wpE 351 c4
  q111 : Ws → Eqn
  q111 c4 = sE 504 (lem-VPQ-at0330 c4)

-- QVQ @0330: 3 steps
lem-QVQ-at0330 : Ws → ⟪ (ℓ "亠产交亠") ⟫ʷ ≈ ⟪ (ℓ "亢产交亢") ⟫ʷ
lem-QVQ-at0330 c4 = derive (ℓ "亠产交亠") (ℓ "亢产交亢")
  (rw⁻ 0 (q110 c4) ∷
   rw⁻ 1 (q111 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = wlE 489 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = sE 503 (lem-VPQ-at0314203142 c4)

-- QVQ @0314203142: 3 steps
lem-QVQ-at0314203142 : Ws → ⟪ (ℓ "交亢亠交") ⟫ʷ ≈ ⟪ (ℓ "产亢亠产") ⟫ʷ
lem-QVQ-at0314203142 c4 = derive (ℓ "交亢亠交") (ℓ "产亢亠产")
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = sE 502 (lem-VPQ-at0310243142 c4)

-- QVQ @0310243142: 3 steps
lem-QVQ-at0310243142 : Ws → ⟪ (ℓ "交亢亠交") ⟫ʷ ≈ ⟪ (ℓ "产亢亠产") ⟫ʷ
lem-QVQ-at0310243142 c4 = derive (ℓ "交亢亠交") (ℓ "产亢亠产")
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q114 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = sE 490 (lem-SWbc-box-at04203243 c4)
  q116 : Ws → Eqn
  q116 c4 = sE 450 (lem-nat-SWbc-at04203243 c4)

-- sym-bc @04203243: 2 steps
lem-sym-bc-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "侓") ⟫ʷ
lem-sym-bc-at04203243 c4 = derive (ℓ "侒") (ℓ "侓")
  (rw⁻ 0 (q115 c4) ∷
   rw 0 (q116 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = sE 489 (lem-SWbc-box-at032032 c4)
  q118 : Ws → Eqn
  q118 c4 = sE 449 (lem-nat-SWbc-at032032 c4)

-- sym-bc @032032: 2 steps
lem-sym-bc-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "佬") ⟫ʷ
lem-sym-bc-at032032 c4 = derive (ℓ "佪") (ℓ "佬")
  (rw⁻ 0 (q117 c4) ∷
   rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = sE 468 (lem-CXbc-box-at0330 c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 382 c4
  q121 : Ws → Eqn
  q121 c4 = sE 476 (lem-CXcb-box-at0330 c4)
  q122 : Ws → Eqn
  q122 c4 = wpE 389 c4
  q123 : Ws → Eqn
  q123 c4 = wpE 381 c4
  q124 : Ws → Eqn
  q124 c4 = wpE 390 c4

-- SWbc-box @0330: 11 steps
lem-SWbc-box-at0330 : Ws → ⟪ (ℓ "串佬串") ⟫ʷ ≈ ⟪ (ℓ "佬") ⟫ʷ
lem-SWbc-box-at0330 c4 = derive (ℓ "串佬串") (ℓ "佬")
  (rw⁻ 0 (q100 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 4 (q122 c4) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q124 c4) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = wpE 257 c4
  q126 : Ws → Eqn
  q126 c4 = sE 461 (lem-CSdu-box-2-at243243 c4)
  q127 : Ws → Eqn
  q127 c4 = sE 498 (lem-Su-box-at243243 c4)

-- XCSX-box-2 @243243: 4 steps
lem-XCSX-box-2-at243243 : Ws → ⟪ (ℓ "並丽並仄") ⟫ʷ ≈ ⟪ (ℓ "仄並丽並") ⟫ʷ
lem-XCSX-box-2-at243243 c4 = derive (ℓ "並丽並仄") (ℓ "仄並丽並")
  (rw⁻ 0 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q125 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = sE 460 (lem-CSdu-box-2-at122441 c4)
  q129 : Ws → Eqn
  q129 c4 = sE 497 (lem-Su-box-at122441 c4)

-- XCSX-box-2 @122441: 4 steps
lem-XCSX-box-2-at122441 : Ws → ⟪ (ℓ "並丽並仞") ⟫ʷ ≈ ⟪ (ℓ "仞並丽並") ⟫ʷ
lem-XCSX-box-2-at122441 c4 = derive (ℓ "並丽並仞") (ℓ "仞並丽並")
  (rw⁻ 0 (q125 c4) ∷
   rw 1 (q128 c4) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q125 c4) ∷ []) Eq.refl

private
  q130 : Ws → Eqn
  q130 c4 = wlE 583 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = sE 459 (lem-CSdu-box-2-at0210243143 c4)
  q132 : Ws → Eqn
  q132 c4 = sE 496 (lem-Su-box-at0210243143 c4)

-- XCSX-box-2 @0210243143: 4 steps
lem-XCSX-box-2-at0210243143 : Ws → ⟪ (ℓ "並乩並伱") ⟫ʷ ≈ ⟪ (ℓ "伱並乩並") ⟫ʷ
lem-XCSX-box-2-at0210243143 c4 = derive (ℓ "並乩並伱") (ℓ "伱並乩並")
  (rw⁻ 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 0 (q132 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = wlE 619 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = sE 467 (lem-CXbc-box-at0214203143 c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 506 c4
  q136 : Ws → Eqn
  q136 c4 = sE 475 (lem-CXcb-box-at0214203143 c4)
  q137 : Ws → Eqn
  q137 c4 = wpE 221 c4
  q138 : Ws → Eqn
  q138 c4 = wpE 507 c4
  q139 : Ws → Eqn
  q139 c4 = wpE 508 c4

-- SWbc-box @0214203143: 11 steps
lem-SWbc-box-at0214203143 : Ws → ⟪ (ℓ "丫佔丫") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-SWbc-box-at0214203143 c4 = derive (ℓ "丫佔丫") (ℓ "佔")
  (rw⁻ 0 (q133 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 4 (q137 c4) ∷
   rw 3 (q138 c4) ∷
   rw 2 (q138 c4) ∷
   rw 3 (q139 c4) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q3 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = wlE 635 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = sE 564 (lem-VPQ-at0214213043 c4)

-- QVQ @0214213043: 3 steps
lem-QVQ-at0214213043 : Ws → ⟪ (ℓ "亘亪亨亘") ⟫ʷ ≈ ⟪ (ℓ "亚亪亨亚") ⟫ʷ
lem-QVQ-at0214213043 c4 = derive (ℓ "亘亪亨亘") (ℓ "亚亪亨亚")
  (rw⁻ 0 (q140 c4) ∷
   rw⁻ 1 (q141 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = wlE 636 (lit c4)
  q143 : Ws → Eqn
  q143 c4 = sE 561 (lem-VPQ-at0210233441 c4)

-- QVQ @0210233441: 3 steps
lem-QVQ-at0210233441 : Ws → ⟪ (ℓ "亨亚亘亨") ⟫ʷ ≈ ⟪ (ℓ "亪亚亘亪") ⟫ʷ
lem-QVQ-at0210233441 c4 = derive (ℓ "亨亚亘亨") (ℓ "亪亚亘亪")
  (rw⁻ 0 (q142 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 4 (q20 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = wlE 649 (lit c4)
  q145 : Ws → Eqn
  q145 c4 = sE 528 (lem-CXbc-box-at122441 c4)
  q146 : Ws → Eqn
  q146 c4 = wlE 650 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = sE 546 (lem-CXcb-box-at122441 c4)
  q148 : Ws → Eqn
  q148 c4 = wlE 651 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = wlE 652 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 653 (lit c4)

-- SWbc-box @122441: 11 steps
lem-SWbc-box-at122441 : Ws → ⟪ (ℓ "乼仞乼") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-SWbc-box-at122441 c4 = derive (ℓ "乼仞乼") (ℓ "仞")
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 3 (q149 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q150 c4) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = sE 570 (lem-VPQ-at12233441 c4)

-- QVQ @12233441: 3 steps
lem-QVQ-at12233441 : Ws → ⟪ (ℓ "五亙亘五") ⟫ʷ ≈ ⟪ (ℓ "井亙亘井") ⟫ʷ
lem-QVQ-at12233441 c4 = derive (ℓ "五亙亘五") (ℓ "井亙亘井")
  (rw⁻ 0 (q34 c4) ∷
   rw⁻ 1 (q151 c4) ∷
   rw 4 (q36 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = wlE 677 (lit c4)
  q153 : Ws → Eqn
  q153 c4 = sE 531 (lem-CXbc-box-at14213243 c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 678 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = sE 549 (lem-CXcb-box-at14213243 c4)
  q156 : Ws → Eqn
  q156 c4 = wlE 679 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = wlE 680 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 681 (lit c4)

-- SWbc-box @14213243: 11 steps
lem-SWbc-box-at14213243 : Ws → ⟪ (ℓ "乊仼乊") ⟫ʷ ≈ ⟪ (ℓ "仼") ⟫ʷ
lem-SWbc-box-at14213243 c4 = derive (ℓ "乊仼乊") (ℓ "仼")
  (rw⁻ 0 (q152 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q154 c4) ∷
   rw 1 (q155 c4) ∷
   rw 4 (q156 c4) ∷
   rw 3 (q157 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q159 : Ws → Eqn
  q159 c4 = sE 572 (lem-VPQ-at143143 c4)

-- QVQ @143143: 3 steps
lem-QVQ-at143143 : Ws → ⟪ (ℓ "亐亝亜亐") ⟫ʷ ≈ ⟪ (ℓ "云亝亜云") ⟫ʷ
lem-QVQ-at143143 c4 = derive (ℓ "亐亝亜亐") (ℓ "云亝亜云")
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = sE 573 (lem-VPQ-at233442 c4)

-- QVQ @233442: 3 steps
lem-QVQ-at233442 : Ws → ⟪ (ℓ "亜云亐亜") ⟫ʷ ≈ ⟪ (ℓ "亝云亐亝") ⟫ʷ
lem-QVQ-at233442 c4 = derive (ℓ "亜云亐亜") (ℓ "亝云亐亝")
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = sE 516 (lem-CXbc-box-at0210243143 c4)
  q162 : Ws → Eqn
  q162 c4 = wpE 566 c4
  q163 : Ws → Eqn
  q163 c4 = sE 535 (lem-CXcb-box-at0210243143 c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 357 c4
  q165 : Ws → Eqn
  q165 c4 = wpE 567 c4
  q166 : Ws → Eqn
  q166 c4 = wpE 568 c4

-- SWbc-box @0210243143: 11 steps
lem-SWbc-box-at0210243143 : Ws → ⟪ (ℓ "乘伱乘") ⟫ʷ ≈ ⟪ (ℓ "伱") ⟫ʷ
lem-SWbc-box-at0210243143 c4 = derive (ℓ "乘伱乘") (ℓ "伱")
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 4 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q166 c4) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q3 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = sE 553 (lem-QVQ-at0210213443 c4)
  q168 : Ws → Eqn
  q168 c4 = sE 124 (lem-tP-at0210213443 c4)

-- box-cP @0210213443: 12 steps
lem-box-cP-at0210213443 : Ws → ⟪ (ℓ "伮") ⟫ʷ ≈ ⟪ (ℓ "二亱二亱") ⟫ʷ
lem-box-cP-at0210213443 c4 = derive (ℓ "伮") (ℓ "二亱二亱")
  (re 0 1 (ℓ "二亏仜亏二仜") ∷
   re 2 1 (ℓ "亜亝仈亝亜仈") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q94 c4) ∷
   re 5 1 (ℓ "亜亝仈亝亜仈") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q94 c4) ∷
   rw 2 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q81 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = wlE 316 (lit c4)
  q170 : Ws → Eqn
  q170 c4 = sE 534 (lem-CXbc-box-at243243 c4)
  q171 : Ws → Eqn
  q171 c4 = sE 552 (lem-CXcb-box-at243243 c4)
  q172 : Ws → Eqn
  q172 c4 = wlE 318 (lit c4)
  q173 : Ws → Eqn
  q173 c4 = wlE 320 (lit c4)

-- SWbc-box @243243: 11 steps
lem-SWbc-box-at243243 : Ws → ⟪ (ℓ "乬仄乬") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-SWbc-box-at243243 c4 = derive (ℓ "乬仄乬") (ℓ "仄")
  (rw⁻ 0 (q169 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q73 c4) ∷
   rw 1 (q171 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q70 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q173 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = sE 532 (lem-CXbc-box-at1441 c4)
  q175 : Ws → Eqn
  q175 c4 = sE 550 (lem-CXcb-box-at1441 c4)

-- SWbc-box @1441: 11 steps
lem-SWbc-box-at1441 : Ws → ⟪ (ℓ "乥伈乥") ⟫ʷ ≈ ⟪ (ℓ "伈") ⟫ʷ
lem-SWbc-box-at1441 c4 = derive (ℓ "乥伈乥") (ℓ "伈")
  (rw⁻ 0 (q13 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q15 c4) ∷
   rw 1 (q175 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = wpE 162 c4
  q177 : Ws → Eqn
  q177 c4 = sE 557 (lem-QVQ-at14233241 c4)
  q178 : Ws → Eqn
  q178 c4 = sE 133 (lem-tP-at14233241 c4)

-- box-cP @14233241: 12 steps
lem-box-cP-at14233241 : Ws → ⟪ (ℓ "伍") ⟫ʷ ≈ ⟪ (ℓ "亠亍亠亍") ⟫ʷ
lem-box-cP-at14233241 c4 = derive (ℓ "伍") (ℓ "亠亍亠亍")
  (re 0 1 (ℓ "亠亡伌亡亠伌") ∷
   re 2 1 (ℓ "亜亟价亟亜价") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q176 c4) ∷
   re 5 1 (ℓ "亜亟价亟亜价") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = sE 569 (lem-VPQ-at12213443 c4)

-- QVQ @12213443: 3 steps
lem-QVQ-at12213443 : Ws → ⟪ (ℓ "亠亍二亠") ⟫ʷ ≈ ⟪ (ℓ "亡亍二亡") ⟫ʷ
lem-QVQ-at12213443 c4 = derive (ℓ "亠亍二亠") (ℓ "亡亍二亡")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q179 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = wlE 714 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wpE 606 c4
  q182 : Ws → Eqn
  q182 c4 = wlE 715 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wpE 607 c4
  q184 : Ws → Eqn
  q184 c4 = wlE 716 (lit c4)

-- F4-CS0-S2: 14 steps
lem-F4-CS0-S2 : Ws → ⟪ (ℓ "並俄並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並俄並") ⟫ʷ
lem-F4-CS0-S2 c4 = derive (ℓ "並俄並乩") (ℓ "乩並俄並")
  (rw⁻ 2 (q180 c4) ∷
   re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q182 c4) ∷
   rw 3 (q183 c4) ∷
   rw⁻ 2 (q182 c4) ∷
   rw⁻ 1 (q132 c4) ∷
   rw⁻ 2 (q131 c4) ∷
   re 5 1 (ℓ "係") ∷
   re 7 1 (ℓ "促") ∷
   re 3 5 (ℓ "俄") ∷
   rw⁻ 0 (q184 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = wpE 602 c4
  q186 : Ws → Eqn
  q186 c4 = wpE 622 c4
  q187 : Ws → Eqn
  q187 c4 = wpE 623 c4
  q188 : Ws → Eqn
  q188 c4 = wpE 624 c4
  q189 : Ws → Eqn
  q189 c4 = wpE 603 c4

-- F4-CS1-S0: 14 steps
lem-F4-CS1-S0 : Ws → ⟪ (ℓ "並侧並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並侧並") ⟫ʷ
lem-F4-CS1-S0 c4 = derive (ℓ "並侧並丽") (ℓ "丽並侧並")
  (rw⁻ 2 (q185 c4) ∷
   re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 5 (q186 c4) ∷
   rw⁻ 4 (q187 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 2 (q187 c4) ∷
   rw⁻ 1 (q127 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   re 5 1 (ℓ "侥") ∷
   re 7 1 (ℓ "侦") ∷
   re 3 5 (ℓ "侧") ∷
   rw⁻ 0 (q189 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = wpE 639 c4
  q191 : Ws → Eqn
  q191 c4 = wpE 640 c4
  q192 : Ws → Eqn
  q192 c4 = wpE 641 c4

-- F4-CS2-S0: 14 steps
lem-F4-CS2-S0 : Ws → ⟪ (ℓ "並侬並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並侬並") ⟫ʷ
lem-F4-CS2-S0 c4 = derive (ℓ "並侬並丽") (ℓ "丽並侬並")
  (rw⁻ 2 (q185 c4) ∷
   re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 5 (q190 c4) ∷
   rw⁻ 4 (q191 c4) ∷
   rw 3 (q192 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw⁻ 1 (q129 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   re 5 1 (ℓ "侪") ∷
   re 7 1 (ℓ "侫") ∷
   re 3 5 (ℓ "侬") ∷
   rw⁻ 0 (q189 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = wlE 755 (lit c4)
  q194 : Ws → Eqn
  q194 c4 = sE 525 (lem-CXbc-box-at0314213042 c4)
  q195 : Ws → Eqn
  q195 c4 = wpE 671 c4
  q196 : Ws → Eqn
  q196 c4 = sE 543 (lem-CXcb-box-at0314213042 c4)
  q197 : Ws → Eqn
  q197 c4 = wpE 672 c4
  q198 : Ws → Eqn
  q198 c4 = wpE 673 c4
  q199 : Ws → Eqn
  q199 c4 = wpE 674 c4

-- SWbc-box @0314213042: 11 steps
lem-SWbc-box-at0314213042 : Ws → ⟪ (ℓ "丫侂丫") ⟫ʷ ≈ ⟪ (ℓ "侂") ⟫ʷ
lem-SWbc-box-at0314213042 c4 = derive (ℓ "丫侂丫") (ℓ "侂")
  (rw⁻ 0 (q193 c4) ∷
   rw⁻ 4 (q193 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw 1 (q196 c4) ∷
   rw 4 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q199 c4) ∷
   rw 0 (q194 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = sE 562 (lem-VPQ-at0213203441 c4)

-- QVQ @0213203441: 3 steps
lem-QVQ-at0213203441 : Ws → ⟪ (ℓ "亨亚亘亨") ⟫ʷ ≈ ⟪ (ℓ "亪亚亘亪") ⟫ʷ
lem-QVQ-at0213203441 c4 = derive (ℓ "亨亚亘亨") (ℓ "亪亚亘亪")
  (rw⁻ 0 (q142 c4) ∷
   rw⁻ 1 (q200 c4) ∷
   rw 4 (q20 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = sE 524 (lem-CXbc-box-at0314203142 c4)
  q202 : Ws → Eqn
  q202 c4 = sE 542 (lem-CXcb-box-at0314203142 c4)
  q203 : Ws → Eqn
  q203 c4 = wpE 22 c4
  q204 : Ws → Eqn
  q204 c4 = wpE 694 c4

-- SWbc-box @0314203142: 11 steps
lem-SWbc-box-at0314203142 : Ws → ⟪ (ℓ "丫佹丫") ⟫ʷ ≈ ⟪ (ℓ "佹") ⟫ʷ
lem-SWbc-box-at0314203142 c4 = derive (ℓ "丫佹丫") (ℓ "佹")
  (rw⁻ 0 (q133 c4) ∷
   rw⁻ 4 (q133 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q198 c4) ∷
   rw 1 (q202 c4) ∷
   rw 4 (q203 c4) ∷
   rw 3 (q195 c4) ∷
   rw 2 (q195 c4) ∷
   rw 3 (q204 c4) ∷
   rw 0 (q201 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = wlE 787 (lit c4)
  q206 : Ws → Eqn
  q206 c4 = sE 568 (lem-VPQ-at0314213042 c4)

-- QVQ @0314213042: 3 steps
lem-QVQ-at0314213042 : Ws → ⟪ (ℓ "亘亮京亘") ⟫ʷ ≈ ⟪ (ℓ "些亮京些") ⟫ʷ
lem-QVQ-at0314213042 c4 = derive (ℓ "亘亮京亘") (ℓ "些亮京些")
  (rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = sE 518 (lem-CXbc-box-at0214213043 c4)
  q208 : Ws → Eqn
  q208 c4 = sE 537 (lem-CXcb-box-at0214213043 c4)
  q209 : Ws → Eqn
  q209 c4 = wpE 712 c4
  q210 : Ws → Eqn
  q210 c4 = wpE 713 c4

-- SWbc-box @0214213043: 11 steps
lem-SWbc-box-at0214213043 : Ws → ⟪ (ℓ "丫佝丫") ⟫ʷ ≈ ⟪ (ℓ "佝") ⟫ʷ
lem-SWbc-box-at0214213043 c4 = derive (ℓ "丫佝丫") (ℓ "佝")
  (rw⁻ 0 (q193 c4) ∷
   rw⁻ 4 (q193 c4) ∷
   rw 2 (q207 c4) ∷
   rw 3 (q138 c4) ∷
   rw 1 (q208 c4) ∷
   rw 4 (q209 c4) ∷
   rw 3 (q135 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q210 c4) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = wlE 835 (lit c4)
  q212 : Ws → Eqn
  q212 c4 = sE 530 (lem-CXbc-box-at1331 c4)
  q213 : Ws → Eqn
  q213 c4 = sE 548 (lem-CXcb-box-at1331 c4)
  q214 : Ws → Eqn
  q214 c4 = wlE 836 (lit c4)
  q215 : Ws → Eqn
  q215 c4 = wlE 837 (lit c4)

-- SWbc-box @1331: 11 steps
lem-SWbc-box-at1331 : Ws → ⟪ (ℓ "乊仭乊") ⟫ʷ ≈ ⟪ (ℓ "仭") ⟫ʷ
lem-SWbc-box-at1331 c4 = derive (ℓ "乊仭乊") (ℓ "仭")
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q212 c4) ∷
   rw 3 (q157 c4) ∷
   rw 1 (q213 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q154 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q215 c4) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = wlE 518 (lit c4)
  q217 : Ws → Eqn
  q217 c4 = sE 556 (lem-QVQ-at032032 c4)
  q218 : Ws → Eqn
  q218 c4 = sE 127 (lem-tP-at032032 c4)

-- box-cP @032032: 12 steps
lem-box-cP-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "亐亲亐亲") ⟫ʷ
lem-box-cP-at032032 c4 = derive (ℓ "佪") (ℓ "亐亲亐亲")
  (re 0 1 (ℓ "亐亓伟亓亐伟") ∷
   re 2 1 (ℓ "交亥伛亥交伛") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q216 c4) ∷
   re 5 1 (ℓ "交亥伛亥交伛") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 1 (q218 c4) ∷
   rw 2 (q92 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = sE 523 (lem-CXbc-box-at0312243140 c4)
  q220 : Ws → Eqn
  q220 c4 = wpE 729 c4
  q221 : Ws → Eqn
  q221 c4 = sE 541 (lem-CXcb-box-at0312243140 c4)
  q222 : Ws → Eqn
  q222 c4 = wpE 285 c4
  q223 : Ws → Eqn
  q223 c4 = wpE 730 c4
  q224 : Ws → Eqn
  q224 c4 = wpE 731 c4

-- SWbc-box @0312243140: 11 steps
lem-SWbc-box-at0312243140 : Ws → ⟪ (ℓ "乘併乘") ⟫ʷ ≈ ⟪ (ℓ "併") ⟫ʷ
lem-SWbc-box-at0312243140 c4 = derive (ℓ "乘併乘") (ℓ "併")
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q219 c4) ∷
   rw 3 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 4 (q222 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw 0 (q219 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q225 : Ws → Eqn
  q225 c4 = sE 522 (lem-CXbc-box-at0312213440 c4)
  q226 : Ws → Eqn
  q226 c4 = sE 540 (lem-CXcb-box-at0312213440 c4)
  q227 : Ws → Eqn
  q227 c4 = wpE 145 c4
  q228 : Ws → Eqn
  q228 c4 = wpE 738 c4
  q229 : Ws → Eqn
  q229 c4 = wlE 341 (lit c4)

-- SWbc-box @0312213440: 11 steps
lem-SWbc-box-at0312213440 : Ws → ⟪ (ℓ "乘佳乘") ⟫ʷ ≈ ⟪ (ℓ "佳") ⟫ʷ
lem-SWbc-box-at0312213440 c4 = derive (ℓ "乘佳乘") (ℓ "佳")
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q225 c4) ∷
   rw 3 (q223 c4) ∷
   rw 1 (q226 c4) ∷
   rw 4 (q227 c4) ∷
   rw 3 (q220 c4) ∷
   rw 2 (q220 c4) ∷
   rw 3 (q228 c4) ∷
   rw 0 (q225 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = sE 567 (lem-VPQ-at0312243140 c4)

-- QVQ @0312243140: 3 steps
lem-QVQ-at0312243140 : Ws → ⟪ (ℓ "亐亲亰亐") ⟫ʷ ≈ ⟪ (ℓ "亓亲亰亓") ⟫ʷ
lem-QVQ-at0312243140 c4 = derive (ℓ "亐亲亰亐") (ℓ "亓亲亰亓")
  (rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q230 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = sE 529 (lem-CXbc-box-at132132 c4)
  q232 : Ws → Eqn
  q232 c4 = sE 547 (lem-CXcb-box-at132132 c4)

-- SWbc-box @132132: 11 steps
lem-SWbc-box-at132132 : Ws → ⟪ (ℓ "乊令乊") ⟫ʷ ≈ ⟪ (ℓ "令") ⟫ʷ
lem-SWbc-box-at132132 c4 = derive (ℓ "乊令乊") (ℓ "令")
  (rw⁻ 0 (q152 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 2 (q231 c4) ∷
   rw 3 (q154 c4) ∷
   rw 1 (q232 c4) ∷
   rw 4 (q156 c4) ∷
   rw 3 (q157 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 0 (q231 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = wlE 923 (lit c4)
  q234 : Ws → Eqn
  q234 c4 = sE 519 (lem-CXbc-box-at022330 c4)
  q235 : Ws → Eqn
  q235 c4 = wpE 762 c4
  q236 : Ws → Eqn
  q236 c4 = sE 538 (lem-CXcb-box-at022330 c4)
  q237 : Ws → Eqn
  q237 c4 = wpE 705 c4
  q238 : Ws → Eqn
  q238 c4 = wpE 763 c4
  q239 : Ws → Eqn
  q239 c4 = wpE 764 c4

-- SWbc-box @022330: 11 steps
lem-SWbc-box-at022330 : Ws → ⟪ (ℓ "丹伴丹") ⟫ʷ ≈ ⟪ (ℓ "伴") ⟫ʷ
lem-SWbc-box-at022330 c4 = derive (ℓ "丹伴丹") (ℓ "伴")
  (rw⁻ 0 (q233 c4) ∷
   rw⁻ 4 (q233 c4) ∷
   rw 2 (q234 c4) ∷
   rw 3 (q235 c4) ∷
   rw 1 (q236 c4) ∷
   rw 4 (q237 c4) ∷
   rw 3 (q238 c4) ∷
   rw 2 (q238 c4) ∷
   rw 3 (q239 c4) ∷
   rw 0 (q234 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = sE 555 (lem-QVQ-at0220 c4)
  q241 : Ws → Eqn
  q241 c4 = sE 125 (lem-tP-at0220 c4)

-- box-cP @0220: 12 steps
lem-box-cP-at0220 : Ws → ⟪ (ℓ "伳") ⟫ʷ ≈ ⟪ (ℓ "二亱二亱") ⟫ʷ
lem-box-cP-at0220 c4 = derive (ℓ "伳") (ℓ "二亱二亱")
  (re 0 1 (ℓ "二亏伕亏二伕") ∷
   re 2 1 (ℓ "交亥休亥交休") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw 2 (q216 c4) ∷
   re 5 1 (ℓ "交亥休亥交休") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw 5 (q216 c4) ∷
   rw 2 (q240 c4) ∷
   rw 1 (q241 c4) ∷
   rw 2 (q81 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = sE 558 (lem-SWbc-box-at0213243140 c4)
  q243 : Ws → Eqn
  q243 c4 = sE 447 (lem-nat-SWbc-at0213243140 c4)

-- sym-bc @0213243140: 2 steps
lem-sym-bc-at0213243140 : Ws → ⟪ (ℓ "低") ⟫ʷ ≈ ⟪ (ℓ "佈") ⟫ʷ
lem-sym-bc-at0213243140 c4 = derive (ℓ "低") (ℓ "佈")
  (rw⁻ 0 (q242 c4) ∷
   rw 0 (q243 c4) ∷ []) Eq.refl

private
  q244 : Ws → Eqn
  q244 c4 = sE 517 (lem-CXbc-box-at0213213440 c4)
  q245 : Ws → Eqn
  q245 c4 = sE 536 (lem-CXcb-box-at0213213440 c4)
  q246 : Ws → Eqn
  q246 c4 = wpE 189 c4
  q247 : Ws → Eqn
  q247 c4 = wpE 769 c4

-- SWbc-box @0213213440: 11 steps
lem-SWbc-box-at0213213440 : Ws → ⟪ (ℓ "乘佈乘") ⟫ʷ ≈ ⟪ (ℓ "佈") ⟫ʷ
lem-SWbc-box-at0213213440 c4 = derive (ℓ "乘佈乘") (ℓ "佈")
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q244 c4) ∷
   rw 3 (q165 c4) ∷
   rw 1 (q245 c4) ∷
   rw 4 (q246 c4) ∷
   rw 3 (q162 c4) ∷
   rw 2 (q162 c4) ∷
   rw 3 (q247 c4) ∷
   rw 0 (q244 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q248 : Ws → Eqn
  q248 c4 = wlE 935 (lit c4)
  q249 : Ws → Eqn
  q249 c4 = sE 554 (lem-QVQ-at0213243140 c4)
  q250 : Ws → Eqn
  q250 c4 = sE 144 (lem-tP-at0213243140 c4)
  q251 : Ws → Eqn
  q251 c4 = wlE 420 (lit c4)

-- box-cP @0213243140: 12 steps
lem-box-cP-at0213243140 : Ws → ⟪ (ℓ "低") ⟫ʷ ≈ ⟪ (ℓ "亰亏亰亏") ⟫ʷ
lem-box-cP-at0213243140 c4 = derive (ℓ "低") (ℓ "亰亏亰亏")
  (re 0 1 (ℓ "亰亱位亱亰位") ∷
   re 2 1 (ℓ "交产伷产交伷") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q248 c4) ∷
   re 5 1 (ℓ "交产伷产交伷") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q248 c4) ∷
   rw 2 (q249 c4) ∷
   rw 1 (q250 c4) ∷
   rw 2 (q251 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = sE 559 (lem-SWbc-box-at0220 c4)
  q253 : Ws → Eqn
  q253 c4 = sE 456 (lem-nat-SWbc-at0220 c4)

-- sym-bc @0220: 2 steps
lem-sym-bc-at0220 : Ws → ⟪ (ℓ "伳") ⟫ʷ ≈ ⟪ (ℓ "伴") ⟫ʷ
lem-sym-bc-at0220 c4 = derive (ℓ "伳") (ℓ "伴")
  (rw⁻ 0 (q252 c4) ∷
   rw 0 (q253 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = wpE 19 c4
  q255 : Ws → Eqn
  q255 c4 = sE 565 (lem-VPQ-at022330 c4)

-- QVQ @022330: 3 steps
lem-QVQ-at022330 : Ws → ⟪ (ℓ "亜亦交亜") ⟫ʷ ≈ ⟪ (ℓ "亞亦交亞") ⟫ʷ
lem-QVQ-at022330 c4 = derive (ℓ "亜亦交亜") (ℓ "亞亦交亞")
  (rw⁻ 0 (q254 c4) ∷
   rw⁻ 1 (q255 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q256 : Ws → Eqn
  q256 c4 = wlE 335 (lit c4)
  q257 : Ws → Eqn
  q257 c4 = sE 526 (lem-CXbc-box-at122331 c4)
  q258 : Ws → Eqn
  q258 c4 = sE 544 (lem-CXcb-box-at122331 c4)
  q259 : Ws → Eqn
  q259 c4 = wlE 336 (lit c4)
  q260 : Ws → Eqn
  q260 c4 = wlE 337 (lit c4)

-- SWbc-box @122331: 11 steps
lem-SWbc-box-at122331 : Ws → ⟪ (ℓ "乑仕乑") ⟫ʷ ≈ ⟪ (ℓ "仕") ⟫ʷ
lem-SWbc-box-at122331 c4 = derive (ℓ "乑仕乑") (ℓ "仕")
  (rw⁻ 0 (q256 c4) ∷
   rw⁻ 4 (q256 c4) ∷
   rw 2 (q257 c4) ∷
   rw 3 (q26 c4) ∷
   rw 1 (q258 c4) ∷
   rw 4 (q259 c4) ∷
   rw 3 (q23 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q260 c4) ∷
   rw 0 (q257 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = sE 571 (lem-VPQ-at14213243 c4)

-- QVQ @14213243: 3 steps
lem-QVQ-at14213243 : Ws → ⟪ (ℓ "亘井五亘") ⟫ʷ ≈ ⟪ (ℓ "亙井五亙") ⟫ʷ
lem-QVQ-at14213243 c4 = derive (ℓ "亘井五亘") (ℓ "亙井五亙")
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q261 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q262 : Ws → Eqn
  q262 c4 = wlE 547 (lit c4)
  q263 : Ws → Eqn
  q263 c4 = sE 527 (lem-CXbc-box-at12233441 c4)
  q264 : Ws → Eqn
  q264 c4 = sE 545 (lem-CXcb-box-at12233441 c4)
  q265 : Ws → Eqn
  q265 c4 = wlE 1008 (lit c4)
  q266 : Ws → Eqn
  q266 c4 = wlE 1009 (lit c4)

-- SWbc-box @12233441: 11 steps
lem-SWbc-box-at12233441 : Ws → ⟪ (ℓ "乼付乼") ⟫ʷ ≈ ⟪ (ℓ "付") ⟫ʷ
lem-SWbc-box-at12233441 c4 = derive (ℓ "乼付乼") (ℓ "付")
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q263 c4) ∷
   rw 3 (q149 c4) ∷
   rw 1 (q264 c4) ∷
   rw 4 (q265 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q266 c4) ∷
   rw 0 (q263 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q267 : Ws → Eqn
  q267 c4 = wlE 1020 (lit c4)
  q268 : Ws → Eqn
  q268 c4 = sE 533 (lem-CXbc-box-at2332 c4)
  q269 : Ws → Eqn
  q269 c4 = sE 551 (lem-CXcb-box-at2332 c4)
  q270 : Ws → Eqn
  q270 c4 = wlE 1021 (lit c4)
  q271 : Ws → Eqn
  q271 c4 = wlE 1022 (lit c4)

-- SWbc-box @2332: 11 steps
lem-SWbc-box-at2332 : Ws → ⟪ (ℓ "乥亾乥") ⟫ʷ ≈ ⟪ (ℓ "亾") ⟫ʷ
lem-SWbc-box-at2332 c4 = derive (ℓ "乥亾乥") (ℓ "亾")
  (rw⁻ 0 (q267 c4) ∷
   rw⁻ 4 (q267 c4) ∷
   rw 2 (q268 c4) ∷
   rw 3 (q18 c4) ∷
   rw 1 (q269 c4) ∷
   rw 4 (q270 c4) ∷
   rw 3 (q15 c4) ∷
   rw 2 (q15 c4) ∷
   rw 3 (q271 c4) ∷
   rw 0 (q268 c4) ∷
   rw 1 (q67 c4) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = sE 465 (lem-CSu-box-2-at243243 c4)
  q273 : Ws → Eqn
  q273 c4 = wpE 393 c4
  q274 : Ws → Eqn
  q274 c4 = wpE 856 c4
  q275 : Ws → Eqn
  q275 c4 = wpE 857 c4

-- F2-S0-CS1: 11 steps
lem-F2-S0-CS1 : Ws → ⟪ (ℓ "丽侧") ⟫ʷ ≈ ⟪ (ℓ "侧丽") ⟫ʷ
lem-F2-S0-CS1 c4 = derive (ℓ "丽侧") (ℓ "侧丽")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 0 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   rw 2 (q274 c4) ∷
   rw 3 (q273 c4) ∷
   rw 4 (q275 c4) ∷
   re 2 1 (ℓ "侥") ∷
   re 4 1 (ℓ "侦") ∷
   re 0 5 (ℓ "侧") ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = sE 464 (lem-CSu-box-2-at122441 c4)
  q277 : Ws → Eqn
  q277 c4 = wpE 858 c4
  q278 : Ws → Eqn
  q278 c4 = wpE 859 c4
  q279 : Ws → Eqn
  q279 c4 = wpE 860 c4

-- F2-S0-CS2: 11 steps
lem-F2-S0-CS2 : Ws → ⟪ (ℓ "丽侬") ⟫ʷ ≈ ⟪ (ℓ "侬丽") ⟫ʷ
lem-F2-S0-CS2 c4 = derive (ℓ "丽侬") (ℓ "侬丽")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw 0 (q276 c4) ∷
   rw 1 (q277 c4) ∷
   rw 2 (q278 c4) ∷
   rw 3 (q277 c4) ∷
   rw 4 (q279 c4) ∷
   re 2 1 (ℓ "侪") ∷
   re 4 1 (ℓ "侫") ∷
   re 0 5 (ℓ "侬") ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = sE 515 (lem-CSu-box-2-at0210243143 c4)
  q281 : Ws → Eqn
  q281 c4 = wlE 754 (lit c4)
  q282 : Ws → Eqn
  q282 c4 = wpE 863 c4
  q283 : Ws → Eqn
  q283 c4 = wpE 864 c4

-- F2-S2-CS0: 11 steps
lem-F2-S2-CS0 : Ws → ⟪ (ℓ "乩俄") ⟫ʷ ≈ ⟪ (ℓ "俄乩") ⟫ʷ
lem-F2-S2-CS0 c4 = derive (ℓ "乩俄") (ℓ "俄乩")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 0 (q280 c4) ∷
   rw 1 (q281 c4) ∷
   rw⁻ 2 (q282 c4) ∷
   rw 3 (q281 c4) ∷
   rw⁻ 4 (q283 c4) ∷
   re 2 1 (ℓ "係") ∷
   re 4 1 (ℓ "促") ∷
   re 0 5 (ℓ "俄") ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = sE 560 (lem-SWbc-box-at03102132 c4)
  q285 : Ws → Eqn
  q285 c4 = sE 448 (lem-nat-SWbc-at03102132 c4)

-- sym-bc @03102132: 2 steps
lem-sym-bc-at03102132 : Ws → ⟪ (ℓ "佤") ⟫ʷ ≈ ⟪ (ℓ "佦") ⟫ʷ
lem-sym-bc-at03102132 c4 = derive (ℓ "佤") (ℓ "佦")
  (rw⁻ 0 (q284 c4) ∷
   rw 0 (q285 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = sE 563 (lem-VPQ-at0214203143 c4)

-- QVQ @0214203143: 3 steps
lem-QVQ-at0214203143 : Ws → ⟪ (ℓ "交亞亜交") ⟫ʷ ≈ ⟪ (ℓ "亦亞亜亦") ⟫ʷ
lem-QVQ-at0214203143 c4 = derive (ℓ "交亞亜交") (ℓ "亦亞亜亦")
  (rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q286 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = sE 520 (lem-CXbc-box-at02233440 c4)
  q288 : Ws → Eqn
  q288 c4 = wpE 916 c4
  q289 : Ws → Eqn
  q289 c4 = sE 539 (lem-CXcb-box-at02233440 c4)
  q290 : Ws → Eqn
  q290 c4 = wpE 523 c4
  q291 : Ws → Eqn
  q291 c4 = wpE 917 c4
  q292 : Ws → Eqn
  q292 c4 = wpE 918 c4

-- SWbc-box @02233440: 11 steps
lem-SWbc-box-at02233440 : Ws → ⟪ (ℓ "乼伵乼") ⟫ʷ ≈ ⟪ (ℓ "伵") ⟫ʷ
lem-SWbc-box-at02233440 c4 = derive (ℓ "乼伵乼") (ℓ "伵")
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q287 c4) ∷
   rw 3 (q288 c4) ∷
   rw 1 (q289 c4) ∷
   rw 4 (q290 c4) ∷
   rw 3 (q291 c4) ∷
   rw 2 (q291 c4) ∷
   rw 3 (q292 c4) ∷
   rw 0 (q287 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = sE 566 (lem-VPQ-at022440 c4)

-- QVQ @022440: 3 steps
lem-QVQ-at022440 : Ws → ⟪ (ℓ "亘亪亨亘") ⟫ʷ ≈ ⟪ (ℓ "亚亪亨亚") ⟫ʷ
lem-QVQ-at022440 c4 = derive (ℓ "亘亪亨亘") (ℓ "亚亪亨亚")
  (rw⁻ 0 (q140 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = sE 521 (lem-CXbc-box-at022440 c4)
  q295 : Ws → Eqn
  q295 c4 = sE 595 (lem-CXcb-box-at022440 c4)
  q296 : Ws → Eqn
  q296 c4 = wpE 810 c4
  q297 : Ws → Eqn
  q297 c4 = wpE 924 c4

-- SWbc-box @022440: 11 steps
lem-SWbc-box-at022440 : Ws → ⟪ (ℓ "乼伶乼") ⟫ʷ ≈ ⟪ (ℓ "伶") ⟫ʷ
lem-SWbc-box-at022440 c4 = derive (ℓ "乼伶乼") (ℓ "伶")
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q294 c4) ∷
   rw 3 (q291 c4) ∷
   rw 1 (q295 c4) ∷
   rw 4 (q296 c4) ∷
   rw 3 (q288 c4) ∷
   rw 2 (q288 c4) ∷
   rw 3 (q297 c4) ∷
   rw 0 (q294 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = sE 615 (lem-VPQ-at02233440 c4)

-- QVQ @02233440: 3 steps
lem-QVQ-at02233440 : Ws → ⟪ (ℓ "亜亦交亜") ⟫ʷ ≈ ⟪ (ℓ "亞亦交亞") ⟫ʷ
lem-QVQ-at02233440 c4 = derive (ℓ "亜亦交亜") (ℓ "亞亦交亞")
  (rw⁻ 0 (q254 c4) ∷
   rw⁻ 1 (q298 c4) ∷
   rw 4 (q31 c4) ∷ []) Eq.refl

private
  q299 : Ws → Eqn
  q299 c4 = sE 626 (lem-VPQ-at1441 c4)

-- QVQ @1441: 3 steps
lem-QVQ-at1441 : Ws → ⟪ (ℓ "亐亝亜亐") ⟫ʷ ≈ ⟪ (ℓ "云亝亜云") ⟫ʷ
lem-QVQ-at1441 c4 = derive (ℓ "亐亝亜亐") (ℓ "云亝亜云")
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q299 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = sE 574 (lem-CXbc-box-at0210233441 c4)
  q301 : Ws → Eqn
  q301 c4 = sE 593 (lem-CXcb-box-at0210233441 c4)

-- SWbc-box @0210233441: 11 steps
lem-SWbc-box-at0210233441 : Ws → ⟪ (ℓ "乼估乼") ⟫ʷ ≈ ⟪ (ℓ "估") ⟫ʷ
lem-SWbc-box-at0210233441 c4 = derive (ℓ "乼估乼") (ℓ "估")
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q300 c4) ∷
   rw 3 (q288 c4) ∷
   rw 1 (q301 c4) ∷
   rw 4 (q290 c4) ∷
   rw 3 (q291 c4) ∷
   rw 2 (q291 c4) ∷
   rw 3 (q292 c4) ∷
   rw 0 (q300 c4) ∷
   rw 1 (q12 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = sE 614 (lem-VPQ-at02102441 c4)

-- QVQ @02102441: 3 steps
lem-QVQ-at02102441 : Ws → ⟪ (ℓ "交亞亜交") ⟫ʷ ≈ ⟪ (ℓ "亦亞亜亦") ⟫ʷ
lem-QVQ-at02102441 c4 = derive (ℓ "交亞亜交") (ℓ "亦亞亜亦")
  (rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q302 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = sE 575 (lem-CXbc-box-at02102441 c4)
  q304 : Ws → Eqn
  q304 c4 = sE 594 (lem-CXcb-box-at02102441 c4)

-- SWbc-box @02102441: 11 steps
lem-SWbc-box-at02102441 : Ws → ⟪ (ℓ "乼伲乼") ⟫ʷ ≈ ⟪ (ℓ "伲") ⟫ʷ
lem-SWbc-box-at02102441 c4 = derive (ℓ "乼伲乼") (ℓ "伲")
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q303 c4) ∷
   rw 3 (q291 c4) ∷
   rw 1 (q304 c4) ∷
   rw 4 (q296 c4) ∷
   rw 3 (q288 c4) ∷
   rw 2 (q288 c4) ∷
   rw 3 (q297 c4) ∷
   rw 0 (q303 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = sE 590 (lem-CXbc-box-at233442 c4)
  q306 : Ws → Eqn
  q306 c4 = sE 609 (lem-CXcb-box-at233442 c4)

-- SWbc-box @233442: 11 steps
lem-SWbc-box-at233442 : Ws → ⟪ (ℓ "乼仂乼") ⟫ʷ ≈ ⟪ (ℓ "仂") ⟫ʷ
lem-SWbc-box-at233442 c4 = derive (ℓ "乼仂乼") (ℓ "仂")
  (rw⁻ 0 (q262 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 2 (q305 c4) ∷
   rw 3 (q149 c4) ∷
   rw 1 (q306 c4) ∷
   rw 4 (q265 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q266 c4) ∷
   rw 0 (q305 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q307 : Ws → Eqn
  q307 c4 = sE 627 (lem-VPQ-at2442 c4)

-- QVQ @2442: 3 steps
lem-QVQ-at2442 : Ws → ⟪ (ℓ "亘井五亘") ⟫ʷ ≈ ⟪ (ℓ "亙井五亙") ⟫ʷ
lem-QVQ-at2442 c4 = derive (ℓ "亘井五亘") (ℓ "亙井五亙")
  (rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q307 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = sE 591 (lem-CXbc-box-at2442 c4)
  q309 : Ws → Eqn
  q309 c4 = sE 610 (lem-CXcb-box-at2442 c4)

-- SWbc-box @2442: 11 steps
lem-SWbc-box-at2442 : Ws → ⟪ (ℓ "乼仆乼") ⟫ʷ ≈ ⟪ (ℓ "仆") ⟫ʷ
lem-SWbc-box-at2442 c4 = derive (ℓ "乼仆乼") (ℓ "仆")
  (rw⁻ 0 (q144 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 2 (q308 c4) ∷
   rw 3 (q146 c4) ∷
   rw 1 (q309 c4) ∷
   rw 4 (q148 c4) ∷
   rw 3 (q149 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q150 c4) ∷
   rw 0 (q308 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q310 : Ws → Eqn
  q310 c4 = sE 589 (lem-CXbc-box-at143143 c4)
  q311 : Ws → Eqn
  q311 c4 = sE 608 (lem-CXcb-box-at143143 c4)

-- SWbc-box @143143: 11 steps
lem-SWbc-box-at143143 : Ws → ⟪ (ℓ "乊伅乊") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-SWbc-box-at143143 c4 = derive (ℓ "乊伅乊") (ℓ "伅")
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q310 c4) ∷
   rw 3 (q157 c4) ∷
   rw 1 (q311 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q154 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q215 c4) ∷
   rw 0 (q310 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q312 : Ws → Eqn
  q312 c4 = sE 588 (lem-CXbc-box-at12213443 c4)
  q313 : Ws → Eqn
  q313 c4 = sE 607 (lem-CXcb-box-at12213443 c4)

-- SWbc-box @12213443: 11 steps
lem-SWbc-box-at12213443 : Ws → ⟪ (ℓ "乘仑乘") ⟫ʷ ≈ ⟪ (ℓ "仑") ⟫ʷ
lem-SWbc-box-at12213443 c4 = derive (ℓ "乘仑乘") (ℓ "仑")
  (rw⁻ 0 (q82 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 2 (q312 c4) ∷
   rw 3 (q45 c4) ∷
   rw 1 (q313 c4) ∷
   rw 4 (q85 c4) ∷
   rw 3 (q42 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q86 c4) ∷
   rw 0 (q312 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q314 : Ws → Eqn
  q314 c4 = sE 625 (lem-VPQ-at12243143 c4)

-- QVQ @12243143: 3 steps
lem-QVQ-at12243143 : Ws → ⟪ (ℓ "亐亝亜亐") ⟫ʷ ≈ ⟪ (ℓ "云亝亜云") ⟫ʷ
lem-QVQ-at12243143 c4 = derive (ℓ "亐亝亜亐") (ℓ "云亝亜云")
  (rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q314 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = sE 613 (lem-SWbc-box-at14233241 c4)
  q316 : Ws → Eqn
  q316 c4 = sE 455 (lem-nat-SWbc-at14233241 c4)

-- sym-bc @14233241: 2 steps
lem-sym-bc-at14233241 : Ws → ⟪ (ℓ "伍") ⟫ʷ ≈ ⟪ (ℓ "伈") ⟫ʷ
lem-sym-bc-at14233241 c4 = derive (ℓ "伍") (ℓ "伈")
  (rw⁻ 0 (q315 c4) ∷
   rw 0 (q316 c4) ∷ []) Eq.refl

private
  q317 : Ws → Eqn
  q317 c4 = sE 585 (lem-CXbc-box-at03143140 c4)
  q318 : Ws → Eqn
  q318 c4 = wpE 653 c4
  q319 : Ws → Eqn
  q319 c4 = sE 604 (lem-CXcb-box-at03143140 c4)
  q320 : Ws → Eqn
  q320 c4 = wpE 749 c4
  q321 : Ws → Eqn
  q321 c4 = wpE 899 c4
  q322 : Ws → Eqn
  q322 c4 = wpE 991 c4

-- SWbc-box @03143140: 11 steps
lem-SWbc-box-at03143140 : Ws → ⟪ (ℓ "乊侌乊") ⟫ʷ ≈ ⟪ (ℓ "侌") ⟫ʷ
lem-SWbc-box-at03143140 c4 = derive (ℓ "乊侌乊") (ℓ "侌")
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q317 c4) ∷
   rw 3 (q318 c4) ∷
   rw 1 (q319 c4) ∷
   rw 4 (q320 c4) ∷
   rw 3 (q321 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q322 c4) ∷
   rw 0 (q317 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = sE 621 (lem-VPQ-at0314213240 c4)

-- QVQ @0314213240: 3 steps
lem-QVQ-at0314213240 : Ws → ⟪ (ℓ "亘亮京亘") ⟫ʷ ≈ ⟪ (ℓ "些亮京些") ⟫ʷ
lem-QVQ-at0314213240 c4 = derive (ℓ "亘亮京亘") (ℓ "些亮京些")
  (rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q323 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = sE 583 (lem-CXbc-box-at0314213240 c4)
  q325 : Ws → Eqn
  q325 c4 = sE 602 (lem-CXcb-box-at0314213240 c4)
  q326 : Ws → Eqn
  q326 c4 = wpE 54 c4
  q327 : Ws → Eqn
  q327 c4 = wpE 900 c4

-- SWbc-box @0314213240: 11 steps
lem-SWbc-box-at0314213240 : Ws → ⟪ (ℓ "乊侅乊") ⟫ʷ ≈ ⟪ (ℓ "侅") ⟫ʷ
lem-SWbc-box-at0314213240 c4 = derive (ℓ "乊侅乊") (ℓ "侅")
  (rw⁻ 0 (q152 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 2 (q324 c4) ∷
   rw 3 (q321 c4) ∷
   rw 1 (q325 c4) ∷
   rw 4 (q326 c4) ∷
   rw 3 (q318 c4) ∷
   rw 2 (q318 c4) ∷
   rw 3 (q327 c4) ∷
   rw 0 (q324 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = sE 622 (lem-VPQ-at03143140 c4)

-- QVQ @03143140: 3 steps
lem-QVQ-at03143140 : Ws → ⟪ (ℓ "亐亲亰亐") ⟫ʷ ≈ ⟪ (ℓ "亓亲亰亓") ⟫ʷ
lem-QVQ-at03143140 c4 = derive (ℓ "亐亲亰亐") (ℓ "亓亲亰亓")
  (rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q329 : Ws → Eqn
  q329 c4 = sE 623 (lem-VPQ-at03243240 c4)

-- QVQ @03243240: 3 steps
lem-QVQ-at03243240 : Ws → ⟪ (ℓ "亘亮京亘") ⟫ʷ ≈ ⟪ (ℓ "些亮京些") ⟫ʷ
lem-QVQ-at03243240 c4 = derive (ℓ "亘亮京亘") (ℓ "些亮京些")
  (rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q329 c4) ∷
   rw 4 (q9 c4) ∷ []) Eq.refl

private
  q330 : Ws → Eqn
  q330 c4 = sE 587 (lem-CXbc-box-at033440 c4)
  q331 : Ws → Eqn
  q331 c4 = wpE 1022 c4
  q332 : Ws → Eqn
  q332 c4 = sE 606 (lem-CXcb-box-at033440 c4)
  q333 : Ws → Eqn
  q333 c4 = wpE 170 c4
  q334 : Ws → Eqn
  q334 c4 = wpE 1023 c4
  q335 : Ws → Eqn
  q335 c4 = wpE 1024 c4

-- SWbc-box @033440: 11 steps
lem-SWbc-box-at033440 : Ws → ⟪ (ℓ "乬佭乬") ⟫ʷ ≈ ⟪ (ℓ "佭") ⟫ʷ
lem-SWbc-box-at033440 c4 = derive (ℓ "乬佭乬") (ℓ "佭")
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q330 c4) ∷
   rw 3 (q331 c4) ∷
   rw 1 (q332 c4) ∷
   rw 4 (q333 c4) ∷
   rw 3 (q334 c4) ∷
   rw 2 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 0 (q330 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = sE 586 (lem-CXbc-box-at03243240 c4)
  q337 : Ws → Eqn
  q337 c4 = sE 605 (lem-CXcb-box-at03243240 c4)
  q338 : Ws → Eqn
  q338 c4 = wpE 269 c4
  q339 : Ws → Eqn
  q339 c4 = wpE 1032 c4

-- SWbc-box @03243240: 11 steps
lem-SWbc-box-at03243240 : Ws → ⟪ (ℓ "乬佯乬") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-SWbc-box-at03243240 c4 = derive (ℓ "乬佯乬") (ℓ "佯")
  (rw⁻ 0 (q169 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 2 (q336 c4) ∷
   rw 3 (q334 c4) ∷
   rw 1 (q337 c4) ∷
   rw 4 (q338 c4) ∷
   rw 3 (q331 c4) ∷
   rw 2 (q331 c4) ∷
   rw 3 (q339 c4) ∷
   rw 0 (q336 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q340 : Ws → Eqn
  q340 c4 = sE 624 (lem-VPQ-at033440 c4)

-- QVQ @033440: 3 steps
lem-QVQ-at033440 : Ws → ⟪ (ℓ "亠产交亠") ⟫ʷ ≈ ⟪ (ℓ "亢产交亢") ⟫ʷ
lem-QVQ-at033440 c4 = derive (ℓ "亠产交亠") (ℓ "亢产交亢")
  (rw⁻ 0 (q110 c4) ∷
   rw⁻ 1 (q340 c4) ∷
   rw 4 (q3 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = sE 580 (lem-CXbc-box-at03103441 c4)
  q342 : Ws → Eqn
  q342 c4 = sE 599 (lem-CXcb-box-at03103441 c4)

-- SWbc-box @03103441: 11 steps
lem-SWbc-box-at03103441 : Ws → ⟪ (ℓ "乬佧乬") ⟫ʷ ≈ ⟪ (ℓ "佧") ⟫ʷ
lem-SWbc-box-at03103441 c4 = derive (ℓ "乬佧乬") (ℓ "佧")
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q341 c4) ∷
   rw 3 (q331 c4) ∷
   rw 1 (q342 c4) ∷
   rw 4 (q333 c4) ∷
   rw 3 (q334 c4) ∷
   rw 2 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 0 (q341 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = sE 616 (lem-VPQ-at0310243241 c4)

-- QVQ @0310243241: 3 steps
lem-QVQ-at0310243241 : Ws → ⟪ (ℓ "交亢亠交") ⟫ʷ ≈ ⟪ (ℓ "产亢亠产") ⟫ʷ
lem-QVQ-at0310243241 c4 = derive (ℓ "交亢亠交") (ℓ "产亢亠产")
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 1 (q343 c4) ∷
   rw 4 (q6 c4) ∷ []) Eq.refl

private
  q344 : Ws → Eqn
  q344 c4 = sE 578 (lem-CXbc-box-at0310243241 c4)
  q345 : Ws → Eqn
  q345 c4 = sE 597 (lem-CXcb-box-at0310243241 c4)

-- SWbc-box @0310243241: 11 steps
lem-SWbc-box-at0310243241 : Ws → ⟪ (ℓ "乬佩乬") ⟫ʷ ≈ ⟪ (ℓ "佩") ⟫ʷ
lem-SWbc-box-at0310243241 c4 = derive (ℓ "乬佩乬") (ℓ "佩")
  (rw⁻ 0 (q169 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 2 (q344 c4) ∷
   rw 3 (q334 c4) ∷
   rw 1 (q345 c4) ∷
   rw 4 (q338 c4) ∷
   rw 3 (q331 c4) ∷
   rw 2 (q331 c4) ∷
   rw 3 (q339 c4) ∷
   rw 0 (q344 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = wlE 788 (lit c4)
  q347 : Ws → Eqn
  q347 c4 = sE 618 (lem-VPQ-at03103441 c4)

-- QVQ @03103441: 3 steps
lem-QVQ-at03103441 : Ws → ⟪ (ℓ "京些亘京") ⟫ʷ ≈ ⟪ (ℓ "亮些亘亮") ⟫ʷ
lem-QVQ-at03103441 c4 = derive (ℓ "京些亘京") (ℓ "亮些亘亮")
  (rw⁻ 0 (q346 c4) ∷
   rw⁻ 1 (q347 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q348 : Ws → Eqn
  q348 c4 = sE 577 (lem-CXbc-box-at0310243142 c4)
  q349 : Ws → Eqn
  q349 c4 = sE 596 (lem-CXcb-box-at0310243142 c4)

-- SWbc-box @0310243142: 11 steps
lem-SWbc-box-at0310243142 : Ws → ⟪ (ℓ "乘佨乘") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-SWbc-box-at0310243142 c4 = derive (ℓ "乘佨乘") (ℓ "佨")
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 2 (q348 c4) ∷
   rw 3 (q220 c4) ∷
   rw 1 (q349 c4) ∷
   rw 4 (q222 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw 0 (q348 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = sE 612 (lem-SWbc-box-at0310213442 c4)
  q351 : Ws → Eqn
  q351 c4 = sE 454 (lem-nat-SWbc-at0310213442 c4)

-- sym-bc @0310213442: 2 steps
lem-sym-bc-at0310213442 : Ws → ⟪ (ℓ "佥") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-sym-bc-at0310213442 c4 = derive (ℓ "佥") (ℓ "佨")
  (rw⁻ 0 (q350 c4) ∷
   rw 0 (q351 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = wpE 1084 c4
  q353 : Ws → Eqn
  q353 c4 = sE 581 (lem-CXbc-box-at0312203441 c4)
  q354 : Ws → Eqn
  q354 c4 = wpE 1085 c4
  q355 : Ws → Eqn
  q355 c4 = sE 600 (lem-CXcb-box-at0312203441 c4)
  q356 : Ws → Eqn
  q356 c4 = wpE 1086 c4
  q357 : Ws → Eqn
  q357 c4 = wpE 1087 c4
  q358 : Ws → Eqn
  q358 c4 = wpE 1088 c4

-- SWbc-box @0312203441: 11 steps
lem-SWbc-box-at0312203441 : Ws → ⟪ (ℓ "乀佱乀") ⟫ʷ ≈ ⟪ (ℓ "佱") ⟫ʷ
lem-SWbc-box-at0312203441 c4 = derive (ℓ "乀佱乀") (ℓ "佱")
  (rw⁻ 0 (q352 c4) ∷
   rw⁻ 4 (q352 c4) ∷
   rw 2 (q353 c4) ∷
   rw 3 (q354 c4) ∷
   rw 1 (q355 c4) ∷
   rw 4 (q356 c4) ∷
   rw 3 (q357 c4) ∷
   rw 2 (q357 c4) ∷
   rw 3 (q358 c4) ∷
   rw 0 (q353 c4) ∷
   rw 1 (q229 c4) ∷ []) Eq.refl

private
  q359 : Ws → Eqn
  q359 c4 = sE 620 (lem-VPQ-at0312243041 c4)

-- QVQ @0312243041: 3 steps
lem-QVQ-at0312243041 : Ws → ⟪ (ℓ "亐亲亰亐") ⟫ʷ ≈ ⟪ (ℓ "亓亲亰亓") ⟫ʷ
lem-QVQ-at0312243041 c4 = derive (ℓ "亐亲亰亐") (ℓ "亓亲亰亓")
  (rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q359 c4) ∷
   rw 4 (q12 c4) ∷ []) Eq.refl

private
  q360 : Ws → Eqn
  q360 c4 = wpE 1101 c4
  q361 : Ws → Eqn
  q361 c4 = sE 582 (lem-CXbc-box-at0312243041 c4)
  q362 : Ws → Eqn
  q362 c4 = sE 601 (lem-CXcb-box-at0312243041 c4)
  q363 : Ws → Eqn
  q363 c4 = wpE 321 c4
  q364 : Ws → Eqn
  q364 c4 = wpE 1102 c4

-- SWbc-box @0312243041: 11 steps
lem-SWbc-box-at0312243041 : Ws → ⟪ (ℓ "乀佴乀") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-SWbc-box-at0312243041 c4 = derive (ℓ "乀佴乀") (ℓ "佴")
  (rw⁻ 0 (q360 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q361 c4) ∷
   rw 3 (q357 c4) ∷
   rw 1 (q362 c4) ∷
   rw 4 (q363 c4) ∷
   rw 3 (q354 c4) ∷
   rw 2 (q354 c4) ∷
   rw 3 (q364 c4) ∷
   rw 0 (q361 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q365 : Ws → Eqn
  q365 c4 = sE 619 (lem-VPQ-at0312203441 c4)

-- QVQ @0312203441: 3 steps
lem-QVQ-at0312203441 : Ws → ⟪ (ℓ "京些亘京") ⟫ʷ ≈ ⟪ (ℓ "亮些亘亮") ⟫ʷ
lem-QVQ-at0312203441 c4 = derive (ℓ "京些亘京") (ℓ "亮些亘亮")
  (rw⁻ 0 (q346 c4) ∷
   rw⁻ 1 (q365 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q366 : Ws → Eqn
  q366 c4 = sE 592 (lem-CXbc-box-at3443 c4)
  q367 : Ws → Eqn
  q367 c4 = sE 611 (lem-CXcb-box-at3443 c4)

-- SWbc-box @3443: 11 steps
lem-SWbc-box-at3443 : Ws → ⟪ (ℓ "乬亼乬") ⟫ʷ ≈ ⟪ (ℓ "亼") ⟫ʷ
lem-SWbc-box-at3443 c4 = derive (ℓ "乬亼乬") (ℓ "亼")
  (rw⁻ 0 (q68 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 2 (q366 c4) ∷
   rw 3 (q70 c4) ∷
   rw 1 (q367 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 0 (q366 c4) ∷
   rw 1 (q6 c4) ∷ []) Eq.refl

private
  q368 : Ws → Eqn
  q368 c4 = sE 579 (lem-CXbc-box-at031031 c4)
  q369 : Ws → Eqn
  q369 c4 = sE 598 (lem-CXcb-box-at031031 c4)

-- SWbc-box @031031: 11 steps
lem-SWbc-box-at031031 : Ws → ⟪ (ℓ "乊佦乊") ⟫ʷ ≈ ⟪ (ℓ "佦") ⟫ʷ
lem-SWbc-box-at031031 c4 = derive (ℓ "乊佦乊") (ℓ "佦")
  (rw⁻ 0 (q211 c4) ∷
   rw⁻ 4 (q211 c4) ∷
   rw 2 (q368 c4) ∷
   rw 3 (q318 c4) ∷
   rw 1 (q369 c4) ∷
   rw 4 (q320 c4) ∷
   rw 3 (q321 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q322 c4) ∷
   rw 0 (q368 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

private
  q370 : Ws → Eqn
  q370 c4 = sE 617 (lem-VPQ-at031031 c4)

-- QVQ @031031: 3 steps
lem-QVQ-at031031 : Ws → ⟪ (ℓ "京些亘京") ⟫ʷ ≈ ⟪ (ℓ "亮些亘亮") ⟫ʷ
lem-QVQ-at031031 c4 = derive (ℓ "京些亘京") (ℓ "亮些亘亮")
  (rw⁻ 0 (q346 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 4 (q67 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = sE 584 (lem-CXbc-box-at03143041 c4)
  q372 : Ws → Eqn
  q372 c4 = sE 603 (lem-CXcb-box-at03143041 c4)

-- SWbc-box @03143041: 11 steps
lem-SWbc-box-at03143041 : Ws → ⟪ (ℓ "串侈串") ⟫ʷ ≈ ⟪ (ℓ "侈") ⟫ʷ
lem-SWbc-box-at03143041 c4 = derive (ℓ "串侈串") (ℓ "侈")
  (rw⁻ 0 (q100 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 2 (q371 c4) ∷
   rw 3 (q120 c4) ∷
   rw 1 (q372 c4) ∷
   rw 4 (q122 c4) ∷
   rw 3 (q123 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q124 c4) ∷
   rw 0 (q371 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

private
  q373 : Ws → Eqn
  q373 c4 = wlE 961 (lit c4)
  q374 : Ws → Eqn
  q374 c4 = sE 576 (lem-CXbc-box-at02142041 c4)
  q375 : Ws → Eqn
  q375 c4 = sE 628 (lem-CXcb-box-at02142041 c4)
  q376 : Ws → Eqn
  q376 c4 = wpE 778 c4
  q377 : Ws → Eqn
  q377 c4 = wpE 779 c4

-- SWbc-box @02142041: 11 steps
lem-SWbc-box-at02142041 : Ws → ⟪ (ℓ "丹余丹") ⟫ʷ ≈ ⟪ (ℓ "余") ⟫ʷ
lem-SWbc-box-at02142041 c4 = derive (ℓ "丹余丹") (ℓ "余")
  (rw⁻ 0 (q373 c4) ∷
   rw⁻ 4 (q373 c4) ∷
   rw 2 (q374 c4) ∷
   rw 3 (q238 c4) ∷
   rw 1 (q375 c4) ∷
   rw 4 (q376 c4) ∷
   rw 3 (q235 c4) ∷
   rw 2 (q235 c4) ∷
   rw 3 (q377 c4) ∷
   rw 0 (q374 c4) ∷
   rw 1 (q36 c4) ∷ []) Eq.refl
