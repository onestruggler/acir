/-
Copyright (c) 2026 QCert contributors. All rights reserved.

Four-wire base cases of (335) and (336). Control-CZ commutation follows
from (150); complementary boxes merge by (170). The different-borrow
cases use (179), (180), and the same merge. Every run is kernel checked.
-/
import QCert.RealCliffordCH.Sec8.D.W4.CommuteLate

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace QCert.RealCliffordCH.Sec8.D.W4Low
open Circuit WE WS
open Eng (L)
open W4
def LControlCZ00 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]]

def RControlCZ00 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ00 : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)]], [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3]])]

theorem runControlCZ00 : check 3 TControlCZ00 LControlCZ00 RControlCZ00
    [.rw 1 0 false,
    .sem 0 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 1 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 2 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .swp 3 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]) true,
    .swp 4 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) true,
    .swp 8 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 9 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 2 [] 0,
    .sem 6 2 [] 0,
    .sem 5 1 [tH 2, tZ 2, tH 2, tH 3, tZ 3, tH 3, tC 2, tH 3, tZ 3, tH 3, tH 2, tZ 2, tH 2] 0,
    .sem 18 1 [tC 0] 2,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sem 6 13 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]] 0,
    .sem 5 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 6 0 [tS 1, tS 1] 0,
    .sem 7 0 [tS 2, tS 2] 0,
    .swp 9 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) false,
    .swp 8 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]) false,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 3 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .sem 4 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 5 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 6 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .swp 7 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]) true,
    .swp 8 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) true,
    .swp 12 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 13 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 11 2 [] 0,
    .sem 10 2 [] 0,
    .sem 9 1 [tH 2, tZ 2, tH 2, tH 3, tZ 3, tH 3, tC 2, tH 3, tZ 3, tH 3, tH 2, tZ 2, tH 2] 0,
    .sem 22 1 [tC 0] 2,
    .sw 21,
    .sw 20,
    .sw 19,
    .sw 18,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sem 10 13 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]] 0,
    .sem 9 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 10 0 [tS 1, tS 1] 0,
    .sem 11 0 [tS 2, tS 2] 0,
    .swp 13 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) false,
    .swp 12 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]) false,
    .swp 8 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 7 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tControlCZ00 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00) (wcT 4 RControlCZ00) :=
  check_sound ih (AllD.cons (t150 ih) (AllD.nil 4)) runControlCZ00

def LControlCZ00f1 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]]

def RControlCZ00f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ00f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ00f1 : check 3 TControlCZ00f1 LControlCZ00f1 RControlCZ00f1
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ00f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f1) (wcT 4 RControlCZ00f1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ00 ih) (AllD.nil 4))) runControlCZ00f1

def LControlCZ00f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]]

def RControlCZ00f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ00f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ00f2 : check 3 TControlCZ00f2 LControlCZ00f2 RControlCZ00f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ00f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f2) (wcT 4 RControlCZ00f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ00 ih) (AllD.nil 4))) runControlCZ00f2

def LControlCZ00f1f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]]

def RControlCZ00f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ00f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ00f1f2 : check 3 TControlCZ00f1f2 LControlCZ00f1f2 RControlCZ00f1f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ00f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f1f2) (wcT 4 RControlCZ00f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ00f1 ih) (AllD.nil 4))) runControlCZ00f1f2

def LControlCZ00f3 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, true)]]

def RControlCZ00f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ00f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ00f3 : check 3 TControlCZ00f3 LControlCZ00f3 RControlCZ00f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ00f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f3) (wcT 4 RControlCZ00f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ00 ih) (AllD.nil 4))) runControlCZ00f3

def LControlCZ00f1f3 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, false)]]

def RControlCZ00f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ00f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ00f1f3 : check 3 TControlCZ00f1f3 LControlCZ00f1f3 RControlCZ00f1f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ00f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f1f3) (wcT 4 RControlCZ00f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ00f1 ih) (AllD.nil 4))) runControlCZ00f1f3

def LControlCZ00f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, true)]]

def RControlCZ00f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ00f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ00f2f3 : check 3 TControlCZ00f2f3 LControlCZ00f2f3 RControlCZ00f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ00f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f2f3) (wcT 4 RControlCZ00f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ00f2 ih) (AllD.nil 4))) runControlCZ00f2f3

def LControlCZ00f1f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, false)]]

def RControlCZ00f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ00f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ00f1f2f3 : check 3 TControlCZ00f1f2f3 LControlCZ00f1f2f3 RControlCZ00f1f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ00f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ00f1f2f3) (wcT 4 RControlCZ00f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ00f1f2 ih) (AllD.nil 4))) runControlCZ00f1f2f3

def LControlCZ01 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]]

def RControlCZ01 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ01 : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)]], [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3]])]

theorem runControlCZ01 : check 3 TControlCZ01 LControlCZ01 RControlCZ01
    [.rw 1 0 false,
    .sem 0 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 1 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 2 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .swp 3 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) true,
    .swp 4 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) true,
    .swp 8 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 9 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 2 [] 0,
    .sem 6 2 [] 0,
    .sem 5 1 [tH 2, tZ 2, tH 2, tC 2, tH 2, tZ 2, tH 2] 0,
    .sem 12 1 [tC 0] 2,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sem 6 7 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]] 0,
    .sem 5 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 6 0 [tS 1, tS 1] 0,
    .sem 7 0 [tS 2, tS 2] 0,
    .swp 9 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) false,
    .swp 8 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) false,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 3 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .sem 4 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 5 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .sem 6 2 [tK 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 3,
    .swp 7 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) true,
    .swp 8 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) true,
    .swp 12 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 13 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 11 2 [] 0,
    .sem 10 2 [] 0,
    .sem 9 1 [tH 2, tZ 2, tH 2, tC 2, tH 2, tZ 2, tH 2] 0,
    .sem 16 1 [tC 0] 2,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sem 10 7 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]] 0,
    .sem 9 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 10 0 [tS 1, tS 1] 0,
    .sem 11 0 [tS 2, tS 2] 0,
    .swp 13 1 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) false,
    .swp 12 2 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) false,
    .swp 8 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 7 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tControlCZ01 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01) (wcT 4 RControlCZ01) :=
  check_sound ih (AllD.cons (t150 ih) (AllD.nil 4)) runControlCZ01

def LControlCZ01f1 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]]

def RControlCZ01f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ01f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ01f1 : check 3 TControlCZ01f1 LControlCZ01f1 RControlCZ01f1
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ01f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f1) (wcT 4 RControlCZ01f1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ01 ih) (AllD.nil 4))) runControlCZ01f1

def LControlCZ01f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]]

def RControlCZ01f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ01f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ01f2 : check 3 TControlCZ01f2 LControlCZ01f2 RControlCZ01f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ01f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f2) (wcT 4 RControlCZ01f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ01 ih) (AllD.nil 4))) runControlCZ01f2

def LControlCZ01f1f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]]

def RControlCZ01f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ01f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ01f1f2 : check 3 TControlCZ01f1f2 LControlCZ01f1f2 RControlCZ01f1f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ01f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f1f2) (wcT 4 RControlCZ01f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ01f1 ih) (AllD.nil 4))) runControlCZ01f1f2

def LControlCZ01f3 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, true)]]

def RControlCZ01f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ01f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ01f3 : check 3 TControlCZ01f3 LControlCZ01f3 RControlCZ01f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ01f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f3) (wcT 4 RControlCZ01f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ01 ih) (AllD.nil 4))) runControlCZ01f3

def LControlCZ01f1f3 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, false)]]

def RControlCZ01f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ01f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ01f1f3 : check 3 TControlCZ01f1f3 LControlCZ01f1f3 RControlCZ01f1f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ01f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f1f3) (wcT 4 RControlCZ01f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ01f1 ih) (AllD.nil 4))) runControlCZ01f1f3

def LControlCZ01f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, true)]]

def RControlCZ01f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ01f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ01f2f3 : check 3 TControlCZ01f2f3 LControlCZ01f2f3 RControlCZ01f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ01f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f2f3) (wcT 4 RControlCZ01f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ01f2 ih) (AllD.nil 4))) runControlCZ01f2f3

def LControlCZ01f1f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, false)]]

def RControlCZ01f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ01f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ01f1f2f3 : check 3 TControlCZ01f1f2f3 LControlCZ01f1f2f3 RControlCZ01f1f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ01f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ01f1f2f3) (wcT 4 RControlCZ01f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ01f1f2 ih) (AllD.nil 4))) runControlCZ01f1f2f3

def LControlCZ10 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]]

def RControlCZ10 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ10 : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)]], [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3]])]

theorem runControlCZ10 : check 3 TControlCZ10 LControlCZ10 RControlCZ10
    [.rw 1 0 false,
    .sem 0 2 [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 3,
    .sem 1 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 3,
    .sem 2 2 [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 3,
    .swp 3 2 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]) true,
    .swp 4 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) true,
    .swp 8 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 9 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 2 [] 0,
    .sem 6 2 [] 0,
    .sem 5 1 [tH 3, tZ 3, tH 3, tC 2, tH 3, tZ 3, tH 3] 0,
    .sem 12 1 [tC 0] 2,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sem 6 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]] 0,
    .sem 5 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 6 0 [tS 1, tS 1] 0,
    .sem 7 0 [tS 2, tS 2] 0,
    .swp 9 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) false,
    .swp 8 2 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]) false,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 3 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .sem 4 2 [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 3,
    .sem 5 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 3,
    .sem 6 2 [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 3,
    .swp 7 2 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]) true,
    .swp 8 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) true,
    .swp 12 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 13 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 11 2 [] 0,
    .sem 10 2 [] 0,
    .sem 9 1 [tH 3, tZ 3, tH 3, tC 2, tH 3, tZ 3, tH 3] 0,
    .sem 16 1 [tC 0] 2,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sem 10 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]] 0,
    .sem 9 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 10 0 [tS 1, tS 1] 0,
    .sem 11 0 [tS 2, tS 2] 0,
    .swp 13 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) false,
    .swp 12 2 (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]) false,
    .swp 8 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 7 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tControlCZ10 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10) (wcT 4 RControlCZ10) :=
  check_sound ih (AllD.cons (t150 ih) (AllD.nil 4)) runControlCZ10

def LControlCZ10f1 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]]

def RControlCZ10f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ10f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ10f1 : check 3 TControlCZ10f1 LControlCZ10f1 RControlCZ10f1
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ10f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f1) (wcT 4 RControlCZ10f1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ10 ih) (AllD.nil 4))) runControlCZ10f1

def LControlCZ10f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]]

def RControlCZ10f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ10f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ10f2 : check 3 TControlCZ10f2 LControlCZ10f2 RControlCZ10f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ10f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f2) (wcT 4 RControlCZ10f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ10 ih) (AllD.nil 4))) runControlCZ10f2

def LControlCZ10f1f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]]

def RControlCZ10f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ10f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ10f1f2 : check 3 TControlCZ10f1f2 LControlCZ10f1f2 RControlCZ10f1f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ10f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f1f2) (wcT 4 RControlCZ10f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ10f1 ih) (AllD.nil 4))) runControlCZ10f1f2

def LControlCZ10f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, true), (1, true)]]

def RControlCZ10f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ10f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ10f3 : check 3 TControlCZ10f3 LControlCZ10f3 RControlCZ10f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ10f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f3) (wcT 4 RControlCZ10f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ10 ih) (AllD.nil 4))) runControlCZ10f3

def LControlCZ10f1f3 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, false)]]

def RControlCZ10f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ10f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ10f1f3 : check 3 TControlCZ10f1f3 LControlCZ10f1f3 RControlCZ10f1f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ10f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f1f3) (wcT 4 RControlCZ10f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ10f1 ih) (AllD.nil 4))) runControlCZ10f1f3

def LControlCZ10f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, true)]]

def RControlCZ10f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ10f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ10f2f3 : check 3 TControlCZ10f2f3 LControlCZ10f2f3 RControlCZ10f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ10f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f2f3) (wcT 4 RControlCZ10f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ10f2 ih) (AllD.nil 4))) runControlCZ10f2f3

def LControlCZ10f1f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, false)]]

def RControlCZ10f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ10f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ10f1f2f3 : check 3 TControlCZ10f1f2f3 LControlCZ10f1f2f3 RControlCZ10f1f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ10f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ10f1f2f3) (wcT 4 RControlCZ10f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ10f1f2 ih) (AllD.nil 4))) runControlCZ10f1f2f3

def LControlCZ11 : List Tk := [tp 2 [L.C 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]]

def RControlCZ11 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.C 0] [1, 2]]

def TControlCZ11 : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)]], [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 3]])]

theorem runControlCZ11 : check 3 TControlCZ11 LControlCZ11 RControlCZ11
    [.rw 1 0 false,
    .sem 0 2 [tK 0, tp 2 [L.C 0] [1, 2]] 3,
    .sem 1 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [1, 2]] 3,
    .sem 2 2 [tK 0, tp 2 [L.C 0] [1, 2]] 3,
    .swp 3 2 (tp 2 [L.C 0] [1, 3]) (tp 2 [L.C 0] [1, 2]) true,
    .swp 4 1 (tp 2 [L.C 0] [2, 3]) (tp 2 [L.C 0] [1, 3]) true,
    .swp 8 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 9 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 2 [] 0,
    .sem 6 2 [] 0,
    .sem 5 1 [tC 2] 0,
    .sem 6 1 [tC 0] 2,
    .sw 5,
    .sem 6 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 5 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 6 0 [tS 1, tS 1] 0,
    .sem 7 0 [tS 2, tS 2] 0,
    .swp 9 1 (tp 2 [L.C 0] [2, 3]) (tp 2 [L.C 0] [1, 3]) false,
    .swp 8 2 (tp 2 [L.C 0] [1, 3]) (tp 2 [L.C 0] [1, 2]) false,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 3 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .sem 4 2 [tK 0, tp 2 [L.C 0] [1, 2]] 3,
    .sem 5 2 [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [1, 2]] 3,
    .sem 6 2 [tK 0, tp 2 [L.C 0] [1, 2]] 3,
    .swp 7 2 (tp 2 [L.C 0] [1, 3]) (tp 2 [L.C 0] [1, 2]) true,
    .swp 8 1 (tp 2 [L.C 0] [2, 3]) (tp 2 [L.C 0] [1, 3]) true,
    .swp 12 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) true,
    .swp 13 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 11 2 [] 0,
    .sem 10 2 [] 0,
    .sem 9 1 [tC 2] 0,
    .sem 10 1 [tC 0] 2,
    .sw 9,
    .sem 10 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 9 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 10 0 [tS 1, tS 1] 0,
    .sem 11 0 [tS 2, tS 2] 0,
    .swp 13 1 (tp 2 [L.C 0] [2, 3]) (tp 2 [L.C 0] [1, 3]) false,
    .swp 12 2 (tp 2 [L.C 0] [1, 3]) (tp 2 [L.C 0] [1, 2]) false,
    .swp 8 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 7 2 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [0, 3]) false,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tControlCZ11 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11) (wcT 4 RControlCZ11) :=
  check_sound ih (AllD.cons (t150 ih) (AllD.nil 4)) runControlCZ11

def LControlCZ11f1 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]]

def RControlCZ11f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ11f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 2 [L.C 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.C 0] [1, 2]])]

theorem runControlCZ11f1 : check 3 TControlCZ11f1 LControlCZ11f1 RControlCZ11f1
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 2 [L.C 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ11f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f1) (wcT 4 RControlCZ11f1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ11 ih) (AllD.nil 4))) runControlCZ11f1

def LControlCZ11f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]]

def RControlCZ11f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ11f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 2 [L.C 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.C 0] [1, 2]])]

theorem runControlCZ11f2 : check 3 TControlCZ11f2 LControlCZ11f2 RControlCZ11f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.C 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ11f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f2) (wcT 4 RControlCZ11f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ11 ih) (AllD.nil 4))) runControlCZ11f2

def LControlCZ11f1f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]]

def RControlCZ11f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ11f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ11f1f2 : check 3 TControlCZ11f1f2 LControlCZ11f1f2 RControlCZ11f1f2
    [.rw 1 0 true,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tControlCZ11f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f1f2) (wcT 4 RControlCZ11f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ11f1 ih) (AllD.nil 4))) runControlCZ11f1f2

def LControlCZ11f3 : List Tk := [tp 2 [L.C 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, true)]]

def RControlCZ11f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tp 2 [L.C 0] [1, 2]]

def TControlCZ11f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 2 [L.C 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.C 0] [1, 2]])]

theorem runControlCZ11f3 : check 3 TControlCZ11f3 LControlCZ11f3 RControlCZ11f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.C 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ11f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f3) (wcT 4 RControlCZ11f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ11 ih) (AllD.nil 4))) runControlCZ11f3

def LControlCZ11f1f3 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, false), (2, true), (1, false)]]

def RControlCZ11f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def TControlCZ11f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]])]

theorem runControlCZ11f1f3 : check 3 TControlCZ11f1f3 LControlCZ11f1f3 RControlCZ11f1f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ11f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f1f3) (wcT 4 RControlCZ11f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ11f1 ih) (AllD.nil 4))) runControlCZ11f1f3

def LControlCZ11f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, true)]]

def RControlCZ11f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ11f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ11f2f3 : check 3 TControlCZ11f2f3 LControlCZ11f2f3 RControlCZ11f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ11f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f2f3) (wcT 4 RControlCZ11f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tControlCZ11f2 ih) (AllD.nil 4))) runControlCZ11f2f3

def LControlCZ11f1f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, false), (2, false), (1, false)]]

def RControlCZ11f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TControlCZ11f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runControlCZ11f1f2f3 : check 3 TControlCZ11f1f2f3 LControlCZ11f1f2f3 RControlCZ11f1f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem tControlCZ11f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LControlCZ11f1f2f3) (wcT 4 RControlCZ11f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tControlCZ11f1f2 ih) (AllD.nil 4))) runControlCZ11f1f2f3

def L166f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def R166f2 : List Tk := []

def T166f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [])]

theorem run166f2 : check 3 T166f2 L166f2 R166f2
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t166f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L166f2) (wcT 4 R166f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (t166 ih) (AllD.nil 4))) run166f2

def L166f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def R166f1f2 : List Tk := []

def T166f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]], [])]

theorem run166f1f2 : check 3 T166f1f2 L166f1f2 R166f1f2
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t166f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L166f1f2) (wcT 4 R166f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (t166f1 ih) (AllD.nil 4))) run166f1f2

def L166f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def R166f3 : List Tk := []

def T166f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [])]

theorem run166f3 : check 3 T166f3 L166f3 R166f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t166f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L166f3) (wcT 4 R166f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (t166 ih) (AllD.nil 4))) run166f3

def L166f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def R166f1f3 : List Tk := []

def T166f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]], [])]

theorem run166f1f3 : check 3 T166f1f3 L166f1f3 R166f1f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t166f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L166f1f3) (wcT 4 R166f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (t166f1 ih) (AllD.nil 4))) run166f1f3

def L166f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def R166f2f3 : List Tk := []

def T166f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [])]

theorem run166f2f3 : check 3 T166f2f3 L166f2f3 R166f2f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t166f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L166f2f3) (wcT 4 R166f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (t166f2 ih) (AllD.nil 4))) run166f2f3

def L166f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def R166f1f2f3 : List Tk := []

def T166f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]], [])]

theorem run166f1f2f3 : check 3 T166f1f2f3 L166f1f2f3 R166f1f2f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t166f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L166f1f2f3) (wcT 4 R166f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (t166f1f2 ih) (AllD.nil 4))) run166f1f2f3

def L170af1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def R170af1f2 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]]

def T170af1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]], [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]])]

theorem run170af1f2 : check 3 T170af1f2 L170af1f2 R170af1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 0 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 2 [] 0] = true := by
  decide +kernel

theorem t170af1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L170af1f2) (wcT 4 R170af1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, false), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (t170af1 ih) (AllD.nil 4)))) run170af1f2

def L170af3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def R170af3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]]

def T170af3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tp 2 [L.C 0] [1, 3]])]

theorem run170af3 : check 3 T170af3 L170af3 R170af3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]] 0] = true := by
  decide +kernel

theorem t170af3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L170af3) (wcT 4 R170af3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (t170a ih) (AllD.nil 4)))) run170af3

def L170af1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def R170af1f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 3]]

def T170af1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]], [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]])]

theorem run170af1f3 : check 3 T170af1f3 L170af1f3 R170af1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 3]] 0] = true := by
  decide +kernel

theorem t170af1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L170af1f3) (wcT 4 R170af1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (t170af1 ih) (AllD.nil 4)))) run170af1f3

def L170af2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def R170af2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]]

def T170af2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [tp 2 [L.C 0] [1, 3]])]

theorem run170af2f3 : check 3 T170af2f3 L170af2f3 R170af2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]] 0] = true := by
  decide +kernel

theorem t170af2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L170af2f3) (wcT 4 R170af2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (t170af2 ih) (AllD.nil 4)))) run170af2f3

def L170af1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def R170af1f2f3 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 3]]

def T170af1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]], [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 3]])]

theorem run170af1f2f3 : check 3 T170af1f2f3 L170af1f2f3 R170af1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 3]] 0] = true := by
  decide +kernel

theorem t170af1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L170af1f2f3) (wcT 4 R170af1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (t170af1f2 ih) (AllD.nil 4)))) run170af1f2f3

def L156f1 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, false)]]

def R156f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f1 : check 3 T156f1 L156f1 R156f1
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 2,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f1) (wcT 4 R156f1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.nil 4))) run156f1

def L156f2 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, false), (1, true)]]

def R156f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f2 : check 3 T156f2 L156f2 R156f2
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f2) (wcT 4 R156f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.nil 4))) run156f2

def L156f1f2 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, false), (1, false)]]

def R156f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f1f2 : check 3 T156f1f2 L156f1f2 R156f1f2
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f1f2) (wcT 4 R156f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (t156f1 ih) (AllD.nil 4))) run156f1f2

def L156f3 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, false), (2, true), (1, true)]]

def R156f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f3 : check 3 T156f3 L156f3 R156f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f3) (wcT 4 R156f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.nil 4))) run156f3

def L156f1f3 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, false), (2, true), (1, false)]]

def R156f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f1f3 : check 3 T156f1f3 L156f1f3 R156f1f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f1f3) (wcT 4 R156f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (t156f1 ih) (AllD.nil 4))) run156f1f3

def L156f2f3 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, false), (2, false), (1, true)]]

def R156f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f2f3 : check 3 T156f2f3 L156f2f3 R156f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f2f3) (wcT 4 R156f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (t156f2 ih) (AllD.nil 4))) run156f2f3

def L156f1f2f3 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, false), (2, false), (1, false)]]

def R156f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T156f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run156f1f2f3 : check 3 T156f1f2f3 L156f1f2f3 R156f1f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t156f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L156f1f2f3) (wcT 4 R156f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (t156f1f2 ih) (AllD.nil 4))) run156f1f2f3

def LBox335BaseTTT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseTTT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseTTT : Tbl := []

theorem runBox335BaseTTT : check 3 TBox335BaseTTT LBox335BaseTTT RBox335BaseTTT
    [] = true := by
  decide +kernel

theorem tBox335BaseTTT (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTT) (wcT 4 RBox335BaseTTT) :=
  check_sound ih (AllD.nil 4) runBox335BaseTTT

def LBox335BaseFTT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseFTT : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseFTT : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (1, true), (2, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (1, false), (2, true)]]),
  ([tg .box [0] [(3, true), (1, true), (2, true)], tg .box [0] [(3, true), (1, false), (2, true)]], [tp 2 [L.C 0] [2, 3]]),
  ([tg .box [0] [(1, true), (3, true), (2, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.C 0] [2, 3], tg .box [0] [(1, true), (3, true), (2, true)]], [tg .box [0] [(1, true), (3, true), (2, true)], tp 2 [L.C 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(1, true), (3, true), (2, true)]])]

theorem runBox335BaseFTT : check 3 TBox335BaseFTT LBox335BaseFTT RBox335BaseFTT
    [.rw 1 0 true,
    .rw 2 1 false,
    .rw 3 2 false,
    .rw 2 3 false,
    .rw 1 4 true,
    .rw 1 5 true,
    .rw 2 6 true,
    .rw 1 3 true,
    .rw 2 2 true,
    .rw 1 1 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseFTT (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTT) (wcT 4 RBox335BaseFTT) :=
  check_sound ih (AllD.cons (t166 ih) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(3, true), (1, true), (2, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, false)] [(3, true), (1, false), (2, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1] (by decide +kernel) (t170a ih)) (AllD.cons (g_entry .box [0] [(1, true), (3, true), (2, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2, 1] (by decide +kernel) (tControlCZ11 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(1, true), (3, true), (2, true)] (by decide +kernel)) (AllD.nil 4)))))))) runBox335BaseFTT

def LBox335BaseTFT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseTFT : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseTFT : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tp 2 [L.C 0] [1, 3]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.C 0] [1, 3], tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)], tp 2 [L.C 0] [1, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)]])]

theorem runBox335BaseTFT : check 3 TBox335BaseTFT LBox335BaseTFT RBox335BaseTFT
    [.rw 1 0 true,
    .rw 2 1 false,
    .rw 1 2 true,
    .rw 1 3 true,
    .rw 2 4 true,
    .rw 1 1 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseTFT (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFT) (wcT 4 RBox335BaseTFT) :=
  check_sound ih (AllD.cons (t166 ih) (AllD.cons (t170a ih) (AllD.cons (g_entry .box [0] [(2, true), (3, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2] (by decide +kernel) (tControlCZ11 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (3, true), (1, true)] (by decide +kernel)) (AllD.nil 4)))))) runBox335BaseTFT

def LBox335BaseTTF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseTTF : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseTTF : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (1, true), (3, true)]]),
  ([tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(2, true), (1, true), (3, false)]]),
  ([tg .box [0] [(2, true), (1, true), (3, true)], tg .box [0] [(2, true), (1, true), (3, false)]], [tg .box [0] [(2, true), (1, true), (3, false)], tg .box [0] [(2, true), (1, true), (3, true)]]),
  ([tg .box [0] [(2, true), (1, true), (3, false)]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(2, true), (1, true), (3, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)]]),
  ([tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, false), (1, true)]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)], tg .box [0] [(2, true), (3, false), (1, true)]], [tp 2 [L.C 0] [1, 2]]),
  ([tp 2 [L.C 0] [1, 2], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.C 0] [1, 2]])]

theorem runBox335BaseTTF : check 3 TBox335BaseTTF LBox335BaseTTF RBox335BaseTTF
    [.rw 1 0 true,
    .rw 2 1 false,
    .rw 3 2 false,
    .rw 2 3 false,
    .rw 2 4 false,
    .rw 3 5 false,
    .rw 2 2 false,
    .rw 3 1 false,
    .rw 2 3 true,
    .rw 2 5 false,
    .rw 3 4 false,
    .rw 2 1 false,
    .rw 3 2 false,
    .rw 2 3 false,
    .rw 2 4 false,
    .rw 3 5 false,
    .rw 2 2 false,
    .rw 3 1 false,
    .rw 2 3 true,
    .rw 2 5 false,
    .rw 3 4 false,
    .rw 2 1 false,
    .rw 3 2 false,
    .rw 2 3 false,
    .rw 2 4 false,
    .rw 3 5 false,
    .rw 2 2 false,
    .rw 3 1 false,
    .rw 2 3 true,
    .rw 2 5 false,
    .rw 3 4 false,
    .rw 2 6 false,
    .rw 3 7 false,
    .rw 2 8 false,
    .rw 1 9 true,
    .rw 1 8 true,
    .rw 2 7 true,
    .rw 1 6 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTF (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTF) (wcT 4 RBox335BaseTTF) :=
  check_sound ih (AllD.cons (t166 ih) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (1, true), (3, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, false), (2, true), (1, true)] [(2, true), (1, true), (3, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1, 2] (by decide +kernel) (tBox335BaseFTT ih)) (AllD.cons (g_entry .box [0] [(2, true), (1, true), (3, false)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(2, true), (1, true), (3, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (3, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, false), (2, true), (1, true)] [(2, true), (3, false), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2] (by decide +kernel) (t170a ih)) (AllD.cons (tControlCZ11 ih) (AllD.nil 4))))))))))) runBox335BaseTTF

def LBox335BaseFFT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseFFT : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseFFT : Tbl := [([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (1, true), (2, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (1, false), (2, false)]]),
  ([tg .box [0] [(3, true), (1, true), (2, false)], tg .box [0] [(3, true), (1, false), (2, false)]], [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]]),
  ([tg .box [0] [(1, true), (3, true), (2, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3], tg .box [0] [(1, true), (3, true), (2, true)]], [tg .box [0] [(1, true), (3, true), (2, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(1, true), (3, true), (2, true)]])]

theorem runBox335BaseFFT : check 3 TBox335BaseFFT LBox335BaseFFT RBox335BaseFFT
    [.rw 0 0 true,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 3 3 false,
    .rw 2 4 false,
    .rw 1 5 true,
    .rw 1 6 true,
    .rw 2 7 true,
    .rw 1 4 true,
    .rw 2 3 true,
    .rw 1 2 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseFFT (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFT) (wcT 4 RBox335BaseFFT) :=
  check_sound ih (AllD.cons (t166f2 ih) (AllD.cons (t170 ih) (AllD.cons (g_entry .box [0] [(3, true), (2, false), (1, true)] [(3, true), (1, true), (2, false)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, true), (2, false), (1, false)] [(3, true), (1, false), (2, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1] (by decide +kernel) (t170af1 ih)) (AllD.cons (g_entry .box [0] [(1, true), (3, true), (2, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2, 1] (by decide +kernel) (tControlCZ01 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(1, true), (3, true), (2, true)] (by decide +kernel)) (AllD.nil 4))))))))) runBox335BaseFFT

def LBox335BaseFTF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseFTF : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseFTF : Tbl := [([tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(2, true), (1, true), (3, false)]]),
  ([tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(2, true), (1, false), (3, false)]]),
  ([tg .box [0] [(2, true), (1, true), (3, false)], tg .box [0] [(2, true), (1, false), (3, false)]], [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 2]]),
  ([tg .box [0] [(1, true), (2, true), (3, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 2], tg .box [0] [(1, true), (2, true), (3, true)]], [tg .box [0] [(1, true), (2, true), (3, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 2]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(1, true), (2, true), (3, true)]])]

theorem runBox335BaseFTF : check 3 TBox335BaseFTF LBox335BaseFTF RBox335BaseFTF
    [.rw 0 0 true,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 3 3 false,
    .rw 2 4 false,
    .sem 2 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]] 0,
    .sem 2 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 2]] 0,
    .rw 1 5 true,
    .rw 1 6 true,
    .rw 2 7 true,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 3]] 0,
    .sem 1 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 2]] 0,
    .rw 1 4 true,
    .rw 2 3 true,
    .rw 1 2 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseFTF (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTF) (wcT 4 RBox335BaseFTF) :=
  check_sound ih (AllD.cons (t166f3 ih) (AllD.cons (tBox335BaseTTF ih) (AllD.cons (g_entry .box [0] [(3, false), (2, true), (1, true)] [(2, true), (1, true), (3, false)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, false), (2, true), (1, false)] [(2, true), (1, false), (3, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1, 2] (by decide +kernel) (t170af1 ih)) (AllD.cons (g_entry .box [0] [(1, true), (2, true), (3, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1, 2, 1] (by decide +kernel) (tControlCZ01 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(1, true), (2, true), (3, true)] (by decide +kernel)) (AllD.nil 4))))))))) runBox335BaseFTF

def LBox335BaseTFF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseTFF : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseTFF : Tbl := [([tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]]),
  ([tg .box [0] [(2, true), (1, true), (3, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 1], tg .box [0] [(2, true), (1, true), (3, true)]], [tg .box [0] [(2, true), (1, true), (3, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 1]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (1, true), (3, true)]])]

theorem runBox335BaseTFF : check 3 TBox335BaseTFF LBox335BaseTFF RBox335BaseTFF
    [.rw 0 0 true,
    .rw 1 1 true,
    .rw 2 2 false,
    .sem 2 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [3, 1]] 0,
    .rw 1 3 true,
    .rw 1 4 true,
    .rw 2 5 true,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 3]] 0,
    .rw 1 2 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseTFF (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFF) (wcT 4 RBox335BaseTFF) :=
  check_sound ih (AllD.cons (t166f3 ih) (AllD.cons (tBox335BaseTTF ih) (AllD.cons (t170af3 ih) (AllD.cons (g_entry .box [0] [(2, true), (1, true), (3, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1, 2] (by decide +kernel) (tControlCZ01 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (1, true), (3, true)] (by decide +kernel)) (AllD.nil 4))))))) runBox335BaseTFF

def LBox335BaseFFF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseFFF : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox335BaseFFF : Tbl := [([tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (1, true), (2, false)]]),
  ([tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (1, false), (2, false)]]),
  ([tg .box [0] [(3, false), (1, true), (2, false)], tg .box [0] [(3, false), (1, false), (2, false)]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [2, 3]]),
  ([tg .box [0] [(1, true), (3, true), (2, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3], tg .box [0] [(1, true), (3, true), (2, true)]], [tg .box [0] [(1, true), (3, true), (2, true)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(1, true), (3, true), (2, true)]])]

theorem runBox335BaseFFF : check 3 TBox335BaseFFF LBox335BaseFFF RBox335BaseFFF
    [.rw 0 0 true,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 3 3 false,
    .rw 2 4 false,
    .sem 2 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [2, 3]] 0,
    .rw 1 5 true,
    .rw 1 6 true,
    .rw 2 7 true,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [2, 3]] 0,
    .rw 1 4 true,
    .rw 2 3 true,
    .rw 1 2 true,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox335BaseFFF (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFF) (wcT 4 RBox335BaseFFF) :=
  check_sound ih (AllD.cons (t166f2f3 ih) (AllD.cons (tBox335BaseTFF ih) (AllD.cons (g_entry .box [0] [(3, false), (2, false), (1, true)] [(3, false), (1, true), (2, false)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, false), (2, false), (1, false)] [(3, false), (1, false), (2, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1] (by decide +kernel) (t170af1f3 ih)) (AllD.cons (g_entry .box [0] [(1, true), (3, true), (2, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2, 1] (by decide +kernel) (tControlCZ00 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(1, true), (3, true), (2, true)] (by decide +kernel)) (AllD.nil 4))))))))) runBox335BaseFFF

def LBox335BaseTTTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseTTTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseTTTf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTTTf1 : check 3 TBox335BaseTTTf1 LBox335BaseTTTf1 RBox335BaseTTTf1
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf1) (wcT 4 RBox335BaseTTTf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTT ih) (AllD.nil 4))) runBox335BaseTTTf1

def LBox335BaseTTTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseTTTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseTTTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTTTf2 : check 3 TBox335BaseTTTf2 LBox335BaseTTTf2 RBox335BaseTTTf2
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf2) (wcT 4 RBox335BaseTTTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTTT ih) (AllD.nil 4))) runBox335BaseTTTf2

def LBox335BaseTTTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseTTTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseTTTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTTTf1f2 : check 3 TBox335BaseTTTf1f2 LBox335BaseTTTf1f2 RBox335BaseTTTf1f2
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf1f2) (wcT 4 RBox335BaseTTTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTTf1 ih) (AllD.nil 4))) runBox335BaseTTTf1f2

def LBox335BaseTTTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseTTTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseTTTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTTTf3 : check 3 TBox335BaseTTTf3 LBox335BaseTTTf3 RBox335BaseTTTf3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf3) (wcT 4 RBox335BaseTTTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTTT ih) (AllD.nil 4))) runBox335BaseTTTf3

def LBox335BaseTTTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseTTTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseTTTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTTTf1f3 : check 3 TBox335BaseTTTf1f3 LBox335BaseTTTf1f3 RBox335BaseTTTf1f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf1f3) (wcT 4 RBox335BaseTTTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTTf1 ih) (AllD.nil 4))) runBox335BaseTTTf1f3

def LBox335BaseTTTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseTTTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseTTTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseTTTf2f3 : check 3 TBox335BaseTTTf2f3 LBox335BaseTTTf2f3 RBox335BaseTTTf2f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf2f3) (wcT 4 RBox335BaseTTTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTTTf2 ih) (AllD.nil 4))) runBox335BaseTTTf2f3

def LBox335BaseTTTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseTTTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseTTTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseTTTf1f2f3 : check 3 TBox335BaseTTTf1f2f3 LBox335BaseTTTf1f2f3 RBox335BaseTTTf1f2f3
    [.rw 1 0 true,
    .rw 0 0 true,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tBox335BaseTTTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTTf1f2f3) (wcT 4 RBox335BaseTTTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTTf1f2 ih) (AllD.nil 4))) runBox335BaseTTTf1f2f3

def LBox335BaseFTTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseFTTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseFTTf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFTTf1 : check 3 TBox335BaseFTTf1 LBox335BaseFTTf1 RBox335BaseFTTf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf1) (wcT 4 RBox335BaseFTTf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTT ih) (AllD.nil 4)))) runBox335BaseFTTf1

def LBox335BaseFTTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseFTTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseFTTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFTTf2 : check 3 TBox335BaseFTTf2 LBox335BaseFTTf2 RBox335BaseFTTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf2) (wcT 4 RBox335BaseFTTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFTT ih) (AllD.nil 4)))) runBox335BaseFTTf2

def LBox335BaseFTTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseFTTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseFTTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFTTf1f2 : check 3 TBox335BaseFTTf1f2 LBox335BaseFTTf1f2 RBox335BaseFTTf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf1f2) (wcT 4 RBox335BaseFTTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTTf1 ih) (AllD.nil 4)))) runBox335BaseFTTf1f2

def LBox335BaseFTTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseFTTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseFTTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFTTf3 : check 3 TBox335BaseFTTf3 LBox335BaseFTTf3 RBox335BaseFTTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf3) (wcT 4 RBox335BaseFTTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFTT ih) (AllD.nil 4)))) runBox335BaseFTTf3

def LBox335BaseFTTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseFTTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseFTTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFTTf1f3 : check 3 TBox335BaseFTTf1f3 LBox335BaseFTTf1f3 RBox335BaseFTTf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf1f3) (wcT 4 RBox335BaseFTTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTTf1 ih) (AllD.nil 4)))) runBox335BaseFTTf1f3

def LBox335BaseFTTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseFTTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseFTTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseFTTf2f3 : check 3 TBox335BaseFTTf2f3 LBox335BaseFTTf2f3 RBox335BaseFTTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf2f3) (wcT 4 RBox335BaseFTTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFTTf2 ih) (AllD.nil 4)))) runBox335BaseFTTf2f3

def LBox335BaseFTTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseFTTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseFTTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseFTTf1f2f3 : check 3 TBox335BaseFTTf1f2f3 LBox335BaseFTTf1f2f3 RBox335BaseFTTf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTTf1f2f3) (wcT 4 RBox335BaseFTTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTTf1f2 ih) (AllD.nil 4)))) runBox335BaseFTTf1f2f3

def LBox335BaseTFTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseTFTf1 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseTFTf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTFTf1 : check 3 TBox335BaseTFTf1 LBox335BaseTFTf1 RBox335BaseTFTf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf1) (wcT 4 RBox335BaseTFTf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, false), (1, true)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (t170 ih) (AllD.nil 4)))) runBox335BaseTFTf1

def LBox335BaseTFTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseTFTf2 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseTFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTFTf2 : check 3 TBox335BaseTFTf2 LBox335BaseTFTf2 RBox335BaseTFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf2) (wcT 4 RBox335BaseTFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, false), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (t170 ih) (AllD.nil 4)))) runBox335BaseTFTf2

def LBox335BaseTFTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseTFTf1f2 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseTFTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTFTf1f2 : check 3 TBox335BaseTFTf1f2 LBox335BaseTFTf1f2 RBox335BaseTFTf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf1f2) (wcT 4 RBox335BaseTFTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, false), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFTf1 ih) (AllD.nil 4)))) runBox335BaseTFTf1f2

def LBox335BaseTFTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseTFTf3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseTFTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTFTf3 : check 3 TBox335BaseTFTf3 LBox335BaseTFTf3 RBox335BaseTFTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf3) (wcT 4 RBox335BaseTFTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (t170 ih) (AllD.nil 4)))) runBox335BaseTFTf3

def LBox335BaseTFTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseTFTf1f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseTFTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTFTf1f3 : check 3 TBox335BaseTFTf1f3 LBox335BaseTFTf1f3 RBox335BaseTFTf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf1f3) (wcT 4 RBox335BaseTFTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFTf1 ih) (AllD.nil 4)))) runBox335BaseTFTf1f3

def LBox335BaseTFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseTFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseTFTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseTFTf2f3 : check 3 TBox335BaseTFTf2f3 LBox335BaseTFTf2f3 RBox335BaseTFTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf2f3) (wcT 4 RBox335BaseTFTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTFTf2 ih) (AllD.nil 4)))) runBox335BaseTFTf2f3

def LBox335BaseTFTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseTFTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseTFTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseTFTf1f2f3 : check 3 TBox335BaseTFTf1f2f3 LBox335BaseTFTf1f2f3 RBox335BaseTFTf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFTf1f2f3) (wcT 4 RBox335BaseTFTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFTf1f2 ih) (AllD.nil 4)))) runBox335BaseTFTf1f2f3

def LBox335BaseTTFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseTTFf1 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseTTFf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTTFf1 : check 3 TBox335BaseTTFf1 LBox335BaseTTFf1 RBox335BaseTTFf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf1) (wcT 4 RBox335BaseTTFf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, false), (2, true), (1, true)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTF ih) (AllD.nil 4)))) runBox335BaseTTFf1

def LBox335BaseTTFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseTTFf2 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseTTFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTTFf2 : check 3 TBox335BaseTTFf2 LBox335BaseTTFf2 RBox335BaseTTFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf2) (wcT 4 RBox335BaseTTFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, true), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTTF ih) (AllD.nil 4)))) runBox335BaseTTFf2

def LBox335BaseTTFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseTTFf1f2 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseTTFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTTFf1f2 : check 3 TBox335BaseTTFf1f2 LBox335BaseTTFf1f2 RBox335BaseTTFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf1f2) (wcT 4 RBox335BaseTTFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, true), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTFf1 ih) (AllD.nil 4)))) runBox335BaseTTFf1f2

def LBox335BaseTTFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseTTFf3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseTTFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTTFf3 : check 3 TBox335BaseTTFf3 LBox335BaseTTFf3 RBox335BaseTTFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf3) (wcT 4 RBox335BaseTTFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTTF ih) (AllD.nil 4)))) runBox335BaseTTFf3

def LBox335BaseTTFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseTTFf1f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseTTFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTTFf1f3 : check 3 TBox335BaseTTFf1f3 LBox335BaseTTFf1f3 RBox335BaseTTFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf1f3) (wcT 4 RBox335BaseTTFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTFf1 ih) (AllD.nil 4)))) runBox335BaseTTFf1f3

def LBox335BaseTTFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseTTFf2f3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseTTFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseTTFf2f3 : check 3 TBox335BaseTTFf2f3 LBox335BaseTTFf2f3 RBox335BaseTTFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf2f3) (wcT 4 RBox335BaseTTFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTTFf2 ih) (AllD.nil 4)))) runBox335BaseTTFf2f3

def LBox335BaseTTFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseTTFf1f2f3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseTTFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseTTFf1f2f3 : check 3 TBox335BaseTTFf1f2f3 LBox335BaseTTFf1f2f3 RBox335BaseTTFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTTFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTTFf1f2f3) (wcT 4 RBox335BaseTTFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTTFf1f2 ih) (AllD.nil 4)))) runBox335BaseTTFf1f2f3

def LBox335BaseFFTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseFFTf1 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseFFTf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFFTf1 : check 3 TBox335BaseFFTf1 LBox335BaseFFTf1 RBox335BaseFFTf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf1) (wcT 4 RBox335BaseFFTf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, false), (1, false)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFT ih) (AllD.nil 4)))) runBox335BaseFFTf1

def LBox335BaseFFTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseFFTf2 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseFFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFFTf2 : check 3 TBox335BaseFFTf2 LBox335BaseFFTf2 RBox335BaseFFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf2) (wcT 4 RBox335BaseFFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, false), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFFT ih) (AllD.nil 4)))) runBox335BaseFFTf2

def LBox335BaseFFTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseFFTf1f2 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseFFTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFFTf1f2 : check 3 TBox335BaseFFTf1f2 LBox335BaseFFTf1f2 RBox335BaseFFTf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf1f2) (wcT 4 RBox335BaseFFTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, false), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFTf1 ih) (AllD.nil 4)))) runBox335BaseFFTf1f2

def LBox335BaseFFTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseFFTf3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseFFTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]], [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFFTf3 : check 3 TBox335BaseFFTf3 LBox335BaseFFTf3 RBox335BaseFFTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf3) (wcT 4 RBox335BaseFFTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFFT ih) (AllD.nil 4)))) runBox335BaseFFTf3

def LBox335BaseFFTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseFFTf1f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseFFTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFFTf1f3 : check 3 TBox335BaseFFTf1f3 LBox335BaseFFTf1f3 RBox335BaseFFTf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf1f3) (wcT 4 RBox335BaseFFTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFTf1 ih) (AllD.nil 4)))) runBox335BaseFFTf1f3

def LBox335BaseFFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseFFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseFFTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseFFTf2f3 : check 3 TBox335BaseFFTf2f3 LBox335BaseFFTf2f3 RBox335BaseFFTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf2f3) (wcT 4 RBox335BaseFFTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFFTf2 ih) (AllD.nil 4)))) runBox335BaseFFTf2f3

def LBox335BaseFFTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseFFTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseFFTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseFFTf1f2f3 : check 3 TBox335BaseFFTf1f2f3 LBox335BaseFFTf1f2f3 RBox335BaseFFTf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFTf1f2f3) (wcT 4 RBox335BaseFFTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFTf1f2 ih) (AllD.nil 4)))) runBox335BaseFFTf1f2f3

def LBox335BaseFTFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseFTFf1 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseFTFf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFTFf1 : check 3 TBox335BaseFTFf1 LBox335BaseFTFf1 RBox335BaseFTFf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf1) (wcT 4 RBox335BaseFTFf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, false), (2, true), (1, false)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTF ih) (AllD.nil 4)))) runBox335BaseFTFf1

def LBox335BaseFTFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseFTFf2 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseFTFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFTFf2 : check 3 TBox335BaseFTFf2 LBox335BaseFTFf2 RBox335BaseFTFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf2) (wcT 4 RBox335BaseFTFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, true), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFTF ih) (AllD.nil 4)))) runBox335BaseFTFf2

def LBox335BaseFTFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseFTFf1f2 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseFTFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFTFf1f2 : check 3 TBox335BaseFTFf1f2 LBox335BaseFTFf1f2 RBox335BaseFTFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf1f2) (wcT 4 RBox335BaseFTFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, true), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTFf1 ih) (AllD.nil 4)))) runBox335BaseFTFf1f2

def LBox335BaseFTFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseFTFf3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseFTFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFTFf3 : check 3 TBox335BaseFTFf3 LBox335BaseFTFf3 RBox335BaseFTFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf3) (wcT 4 RBox335BaseFTFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFTF ih) (AllD.nil 4)))) runBox335BaseFTFf3

def LBox335BaseFTFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseFTFf1f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseFTFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFTFf1f3 : check 3 TBox335BaseFTFf1f3 LBox335BaseFTFf1f3 RBox335BaseFTFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf1f3) (wcT 4 RBox335BaseFTFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTFf1 ih) (AllD.nil 4)))) runBox335BaseFTFf1f3

def LBox335BaseFTFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseFTFf2f3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseFTFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseFTFf2f3 : check 3 TBox335BaseFTFf2f3 LBox335BaseFTFf2f3 RBox335BaseFTFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf2f3) (wcT 4 RBox335BaseFTFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFTFf2 ih) (AllD.nil 4)))) runBox335BaseFTFf2f3

def LBox335BaseFTFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseFTFf1f2f3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseFTFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseFTFf1f2f3 : check 3 TBox335BaseFTFf1f2f3 LBox335BaseFTFf1f2f3 RBox335BaseFTFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFTFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFTFf1f2f3) (wcT 4 RBox335BaseFTFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFTFf1f2 ih) (AllD.nil 4)))) runBox335BaseFTFf1f2f3

def LBox335BaseTFFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def RBox335BaseTFFf1 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseTFFf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTFFf1 : check 3 TBox335BaseTFFf1 LBox335BaseTFFf1 RBox335BaseTFFf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf1) (wcT 4 RBox335BaseTFFf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, false), (2, false), (1, true)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFF ih) (AllD.nil 4)))) runBox335BaseTFFf1

def LBox335BaseTFFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseTFFf2 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseTFFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTFFf2 : check 3 TBox335BaseTFFf2 LBox335BaseTFFf2 RBox335BaseTFFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf2) (wcT 4 RBox335BaseTFFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, false), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTFF ih) (AllD.nil 4)))) runBox335BaseTFFf2

def LBox335BaseTFFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseTFFf1f2 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseTFFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTFFf1f2 : check 3 TBox335BaseTFFf1f2 LBox335BaseTFFf1f2 RBox335BaseTFFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf1f2) (wcT 4 RBox335BaseTFFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, false), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFFf1 ih) (AllD.nil 4)))) runBox335BaseTFFf1f2

def LBox335BaseTFFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseTFFf3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseTFFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseTFFf3 : check 3 TBox335BaseTFFf3 LBox335BaseTFFf3 RBox335BaseTFFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf3) (wcT 4 RBox335BaseTFFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTFF ih) (AllD.nil 4)))) runBox335BaseTFFf3

def LBox335BaseTFFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseTFFf1f3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseTFFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseTFFf1f3 : check 3 TBox335BaseTFFf1f3 LBox335BaseTFFf1f3 RBox335BaseTFFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf1f3) (wcT 4 RBox335BaseTFFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFFf1 ih) (AllD.nil 4)))) runBox335BaseTFFf1f3

def LBox335BaseTFFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseTFFf2f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseTFFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseTFFf2f3 : check 3 TBox335BaseTFFf2f3 LBox335BaseTFFf2f3 RBox335BaseTFFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf2f3) (wcT 4 RBox335BaseTFFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseTFFf2 ih) (AllD.nil 4)))) runBox335BaseTFFf2f3

def LBox335BaseTFFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseTFFf1f2f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseTFFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseTFFf1f2f3 : check 3 TBox335BaseTFFf1f2f3 LBox335BaseTFFf1f2f3 RBox335BaseTFFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseTFFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseTFFf1f2f3) (wcT 4 RBox335BaseTFFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseTFFf1f2 ih) (AllD.nil 4)))) runBox335BaseTFFf1f2f3

def LBox335BaseFFFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def RBox335BaseFFFf1 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox335BaseFFFf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFFFf1 : check 3 TBox335BaseFFFf1 LBox335BaseFFFf1 RBox335BaseFFFf1
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf1) (wcT 4 RBox335BaseFFFf1) :=
  check_sound ih (AllD.cons (x81_entry 1 .box [0] [(3, false), (2, false), (1, false)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFF ih) (AllD.nil 4)))) runBox335BaseFFFf1

def LBox335BaseFFFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def RBox335BaseFFFf2 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox335BaseFFFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFFFf2 : check 3 TBox335BaseFFFf2 LBox335BaseFFFf2 RBox335BaseFFFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf2) (wcT 4 RBox335BaseFFFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, false), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFFF ih) (AllD.nil 4)))) runBox335BaseFFFf2

def LBox335BaseFFFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def RBox335BaseFFFf1f2 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox335BaseFFFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFFFf1f2 : check 3 TBox335BaseFFFf1f2 LBox335BaseFFFf1f2 RBox335BaseFFFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf1f2) (wcT 4 RBox335BaseFFFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, false), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFFf1 ih) (AllD.nil 4)))) runBox335BaseFFFf1f2

def LBox335BaseFFFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def RBox335BaseFFFf3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox335BaseFFFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]], [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox335BaseFFFf3 : check 3 TBox335BaseFFFf3 LBox335BaseFFFf3 RBox335BaseFFFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf3) (wcT 4 RBox335BaseFFFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFFF ih) (AllD.nil 4)))) runBox335BaseFFFf3

def LBox335BaseFFFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def RBox335BaseFFFf1f3 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox335BaseFFFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox335BaseFFFf1f3 : check 3 TBox335BaseFFFf1f3 LBox335BaseFFFf1f3 RBox335BaseFFFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf1f3) (wcT 4 RBox335BaseFFFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, false), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFFf1 ih) (AllD.nil 4)))) runBox335BaseFFFf1f3

def LBox335BaseFFFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def RBox335BaseFFFf2f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox335BaseFFFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [0] [(3, false), (2, true), (1, false)]], [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox335BaseFFFf2f3 : check 3 TBox335BaseFFFf2f3 LBox335BaseFFFf2f3 RBox335BaseFFFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf2f3) (wcT 4 RBox335BaseFFFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, false)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox335BaseFFFf2 ih) (AllD.nil 4)))) runBox335BaseFFFf2f3

def LBox335BaseFFFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def RBox335BaseFFFf1f2f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox335BaseFFFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox335BaseFFFf1f2f3 : check 3 TBox335BaseFFFf1f2f3 LBox335BaseFFFf1f2f3 RBox335BaseFFFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox335BaseFFFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox335BaseFFFf1f2f3) (wcT 4 RBox335BaseFFFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox335BaseFFFf1f2 ih) (AllD.nil 4)))) runBox335BaseFFFf1f2f3

def LBox336BaseTFT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTFT : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTFT : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFT : check 3 TBox336BaseTFT LBox336BaseTFT RBox336BaseTFT
    [.rw 0 0 false] = true := by
  decide +kernel

theorem tBox336BaseTFT (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFT) (wcT 4 RBox336BaseTFT) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t179 ih)) (AllD.nil 4)) runBox336BaseTFT

def LBox336BaseTTF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTTF : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTTF : Tbl := [([tg .box [1] [(2, true), (3, false), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)], tg .box [1] [(2, true), (3, false), (0, true)]], [tg .box [1] [(2, true), (3, false), (0, true)], tg .box [0] [(2, true), (3, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)]]),
  ([tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(2, true), (3, false), (0, true)]])]

theorem runBox336BaseTTF : check 3 TBox336BaseTTF LBox336BaseTTF RBox336BaseTTF
    [.rw 1 0 true,
    .rw 0 1 true,
    .rw 0 2 false,
    .rw 1 3 true,
    .rw 0 4 true] = true := by
  decide +kernel

theorem tBox336BaseTTF (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTF) (wcT 4 RBox336BaseTTF) :=
  check_sound ih (AllD.cons (g_entry .box [1] [(2, true), (3, false), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(2, true), (3, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0, 2] (by decide +kernel) (t179 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (3, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .box [1] [(3, false), (2, true), (0, true)] [(2, true), (3, false), (0, true)] (by decide +kernel)) (AllD.nil 4)))))) runBox336BaseTTF

def LBox336BaseTFF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTFF : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTFF : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFF : check 3 TBox336BaseTFF LBox336BaseTFF RBox336BaseTFF
    [.rw 0 0 false] = true := by
  decide +kernel

theorem tBox336BaseTFF (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFF) (wcT 4 RBox336BaseTFF) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t180 ih)) (AllD.nil 4)) runBox336BaseTFF

def LBox336BaseTTT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTTT : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTTT : Tbl := [([tg .box [1] [(3, true), (0, true), (2, false)], tg .box [1] [(3, true), (0, true), (2, false)]], []),
  ([tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (0, true), (2, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .box [1] [(3, true), (2, false), (0, true)], tg .box [1] [(3, true), (2, true), (0, true)]], [tp 2 [L.C 0] [0, 3]]),
  ([tg .box [1] [(3, true), (2, true), (0, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tp 2 [L.C 0] [0, 3]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 2 [L.C 0] [0, 3], tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)], tp 2 [L.C 0] [0, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)]])]

theorem runBox336BaseTTT : check 3 TBox336BaseTTT LBox336BaseTTT RBox336BaseTTT
    [.rw 0 0 true,
    .rw 1 1 true,
    .rw 0 1 true,
    .rw 1 2 true,
    .rw 2 3 false,
    .rw 2 4 true,
    .rw 2 4 false,
    .rw 1 5 true,
    .rw 1 6 true,
    .rw 2 7 true,
    .rw 1 4 true,
    .rw 1 4 false,
    .rw 1 3 true,
    .rw 0 1 false,
    .rw 1 1 false,
    .rw 0 0 false] = true := by
  decide +kernel

theorem tBox336BaseTTT (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTT) (wcT 4 RBox336BaseTTT) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [1, 0] (by decide +kernel) (t166f1 ih)) (AllD.cons (g_entry .box [1] [(3, true), (2, false), (0, true)] [(3, true), (0, true), (2, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t179 ih)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t170af2 ih)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t170a ih)) (AllD.cons (g_entry .box [0] [(2, true), (3, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2] (by decide +kernel) (t159 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (3, true), (1, true)] (by decide +kernel)) (AllD.nil 4))))))))) runBox336BaseTTT

def LBox336BaseTFTf0 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTFTf0 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTFTf0 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf0 : check 3 TBox336BaseTFTf0 LBox336BaseTFTf0 RBox336BaseTFTf0
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 1 true,
    .sem 2 2 [] 1,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 0 false,
    .rw 1 1 false,
    .sem 2 2 [] 1] = true := by
  decide +kernel

theorem tBox336BaseTFTf0 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0) (wcT 4 RBox336BaseTFTf0) :=
  check_sound ih (AllD.cons (x81_entry 0 .box [1] [(3, true), (2, false), (0, true)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t179 ih)) (AllD.nil 4)))) runBox336BaseTFTf0

def LBox336BaseTFTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTFTf1 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTFTf1 : Tbl := [([tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (0, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(3, true), (0, true), (2, false)]], [tg .box [1] [(3, true), (0, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tg .box [1] [(3, true), (0, true), (2, false)]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf1 : check 3 TBox336BaseTFTf1 LBox336BaseTFTf1 RBox336BaseTFTf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 false,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 0 3 true,
    .sem 2 2 [] 0,
    .rw 1 4 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 2 true,
    .rw 0 1 false,
    .rw 0 0 true,
    .sem 1 2 [] 0,
    .rw 1 3 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf1) (wcT 4 RBox336BaseTFTf1) :=
  check_sound ih (AllD.cons (g_entry .box [1] [(3, true), (2, false), (0, true)] [(3, true), (0, true), (2, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1, 0] (by decide +kernel) (t156f1 ih)) (AllD.cons (g_entry .box [1] [(3, true), (0, true), (2, false)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t179 ih)) (AllD.nil 4)))))) runBox336BaseTFTf1

def LBox336BaseTFTf0f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTFTf0f1 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTFTf0f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf0f1 : check 3 TBox336BaseTFTf0f1 LBox336BaseTFTf0f1 RBox336BaseTFTf0f1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [] 0,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f1) (wcT 4 RBox336BaseTFTf0f1) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t156f1f2 ih)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0 ih) (AllD.nil 4)))) runBox336BaseTFTf0f1

def LBox336BaseTFTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTFTf2 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf2 : check 3 TBox336BaseTFTf2 LBox336BaseTFTf2 RBox336BaseTFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf2) (wcT 4 RBox336BaseTFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, false), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t179 ih)) (AllD.nil 4)))) runBox336BaseTFTf2

def LBox336BaseTFTf0f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTFTf0f2 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTFTf0f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf0f2 : check 3 TBox336BaseTFTf0f2 LBox336BaseTFTf0f2 RBox336BaseTFTf0f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f2) (wcT 4 RBox336BaseTFTf0f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, false), (0, false)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0 ih) (AllD.nil 4)))) runBox336BaseTFTf0f2

def LBox336BaseTFTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTFTf1f2 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTFTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFTf1f2 : check 3 TBox336BaseTFTf1f2 LBox336BaseTFTf1f2 RBox336BaseTFTf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf1f2) (wcT 4 RBox336BaseTFTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, false), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf1 ih) (AllD.nil 4)))) runBox336BaseTFTf1f2

def LBox336BaseTFTf0f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTFTf0f1f2 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTFTf0f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFTf0f1f2 : check 3 TBox336BaseTFTf0f1f2 LBox336BaseTFTf0f1f2 RBox336BaseTFTf0f1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f1f2) (wcT 4 RBox336BaseTFTf0f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, false), (0, false)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0f1 ih) (AllD.nil 4)))) runBox336BaseTFTf0f1f2

def LBox336BaseTFTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTFTf3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTFTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf3 : check 3 TBox336BaseTFTf3 LBox336BaseTFTf3 RBox336BaseTFTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf3) (wcT 4 RBox336BaseTFTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, true)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t179 ih)) (AllD.nil 4)))) runBox336BaseTFTf3

def LBox336BaseTFTf0f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTFTf0f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTFTf0f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFTf0f3 : check 3 TBox336BaseTFTf0f3 LBox336BaseTFTf0f3 RBox336BaseTFTf0f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f3) (wcT 4 RBox336BaseTFTf0f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, false)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0 ih) (AllD.nil 4)))) runBox336BaseTFTf0f3

def LBox336BaseTFTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTFTf1f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTFTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFTf1f3 : check 3 TBox336BaseTFTf1f3 LBox336BaseTFTf1f3 RBox336BaseTFTf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf1f3) (wcT 4 RBox336BaseTFTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, true)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf1 ih) (AllD.nil 4)))) runBox336BaseTFTf1f3

def LBox336BaseTFTf0f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTFTf0f1f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTFTf0f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFTf0f1f3 : check 3 TBox336BaseTFTf0f1f3 LBox336BaseTFTf0f1f3 RBox336BaseTFTf0f1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f1f3) (wcT 4 RBox336BaseTFTf0f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, false)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0f1 ih) (AllD.nil 4)))) runBox336BaseTFTf0f1f3

def LBox336BaseTFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTFTf2f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTFTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTFTf2f3 : check 3 TBox336BaseTFTf2f3 LBox336BaseTFTf2f3 RBox336BaseTFTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf2f3) (wcT 4 RBox336BaseTFTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf2 ih) (AllD.nil 4)))) runBox336BaseTFTf2f3

def LBox336BaseTFTf0f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTFTf0f2f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTFTf0f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTFTf0f2f3 : check 3 TBox336BaseTFTf0f2f3 LBox336BaseTFTf0f2f3 RBox336BaseTFTf0f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f2f3) (wcT 4 RBox336BaseTFTf0f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0f2 ih) (AllD.nil 4)))) runBox336BaseTFTf0f2f3

def LBox336BaseTFTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTFTf1f2f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTFTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTFTf1f2f3 : check 3 TBox336BaseTFTf1f2f3 LBox336BaseTFTf1f2f3 RBox336BaseTFTf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf1f2f3) (wcT 4 RBox336BaseTFTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf1f2 ih) (AllD.nil 4)))) runBox336BaseTFTf1f2f3

def LBox336BaseTFTf0f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTFTf0f1f2f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTFTf0f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTFTf0f1f2f3 : check 3 TBox336BaseTFTf0f1f2f3 LBox336BaseTFTf0f1f2f3 RBox336BaseTFTf0f1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFTf0f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFTf0f1f2f3) (wcT 4 RBox336BaseTFTf0f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFTf0f1f2 ih) (AllD.nil 4)))) runBox336BaseTFTf0f1f2f3

def LBox336BaseTTFf0 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTTFf0 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTTFf0 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf0 : check 3 TBox336BaseTTFf0 LBox336BaseTTFf0 RBox336BaseTTFf0
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 1 true,
    .sem 2 2 [] 1,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 0 false,
    .rw 1 1 false,
    .sem 2 2 [] 1] = true := by
  decide +kernel

theorem tBox336BaseTTFf0 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0) (wcT 4 RBox336BaseTTFf0) :=
  check_sound ih (AllD.cons (x81_entry 0 .box [1] [(3, false), (2, true), (0, true)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.cons (tBox336BaseTTF ih) (AllD.nil 4)))) runBox336BaseTTFf0

def LBox336BaseTTFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTTFf1 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTTFf1 : Tbl := [([tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(2, true), (0, true), (3, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(2, true), (0, true), (3, false)]], [tg .box [1] [(2, true), (0, true), (3, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tg .box [1] [(2, true), (0, true), (3, false)]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf1 : check 3 TBox336BaseTTFf1 LBox336BaseTTFf1 RBox336BaseTTFf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 false,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 0 3 true,
    .sem 2 2 [] 0,
    .rw 1 4 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 2 true,
    .rw 0 1 false,
    .rw 0 0 true,
    .sem 1 2 [] 0,
    .rw 1 3 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf1) (wcT 4 RBox336BaseTTFf1) :=
  check_sound ih (AllD.cons (g_entry .box [1] [(3, false), (2, true), (0, true)] [(2, true), (0, true), (3, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [1, 0, 2] (by decide +kernel) (t156f1 ih)) (AllD.cons (g_entry .box [1] [(2, true), (0, true), (3, false)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTF ih) (AllD.nil 4)))))) runBox336BaseTTFf1

def LBox336BaseTTFf0f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTTFf0f1 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTTFf0f1 : Tbl := [([tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(2, true), (3, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(2, true), (3, false), (0, false)]], [tg .box [1] [(2, true), (3, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tg .box [1] [(2, true), (3, false), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf0f1 : check 3 TBox336BaseTTFf0f1 LBox336BaseTTFf0f1 RBox336BaseTTFf0f1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 false,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 0 3 true,
    .sem 2 2 [] 0,
    .rw 1 4 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 2 true,
    .rw 0 1 false,
    .rw 0 0 true,
    .sem 1 2 [] 0,
    .rw 1 3 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f1) (wcT 4 RBox336BaseTTFf0f1) :=
  check_sound ih (AllD.cons (g_entry .box [1] [(3, false), (2, true), (0, false)] [(2, true), (3, false), (0, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0, 2] (by decide +kernel) (t156f1f2 ih)) (AllD.cons (g_entry .box [1] [(2, true), (3, false), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0 ih) (AllD.nil 4)))))) runBox336BaseTTFf0f1

def LBox336BaseTTFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTTFf2 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTTFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf2 : check 3 TBox336BaseTTFf2 LBox336BaseTTFf2 RBox336BaseTTFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf2) (wcT 4 RBox336BaseTTFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, true), (0, true)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTF ih) (AllD.nil 4)))) runBox336BaseTTFf2

def LBox336BaseTTFf0f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTTFf0f2 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTTFf0f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf0f2 : check 3 TBox336BaseTTFf0f2 LBox336BaseTTFf0f2 RBox336BaseTTFf0f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f2) (wcT 4 RBox336BaseTTFf0f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, true), (0, false)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0 ih) (AllD.nil 4)))) runBox336BaseTTFf0f2

def LBox336BaseTTFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTTFf1f2 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTTFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTFf1f2 : check 3 TBox336BaseTTFf1f2 LBox336BaseTTFf1f2 RBox336BaseTTFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf1f2) (wcT 4 RBox336BaseTTFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, true), (0, true)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf1 ih) (AllD.nil 4)))) runBox336BaseTTFf1f2

def LBox336BaseTTFf0f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTTFf0f1f2 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTTFf0f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTFf0f1f2 : check 3 TBox336BaseTTFf0f1f2 LBox336BaseTTFf0f1f2 RBox336BaseTTFf0f1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f1f2) (wcT 4 RBox336BaseTTFf0f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, true), (0, false)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0f1 ih) (AllD.nil 4)))) runBox336BaseTTFf0f1f2

def LBox336BaseTTFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTTFf3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTTFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf3 : check 3 TBox336BaseTTFf3 LBox336BaseTTFf3 RBox336BaseTTFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf3) (wcT 4 RBox336BaseTTFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTF ih) (AllD.nil 4)))) runBox336BaseTTFf3

def LBox336BaseTTFf0f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTTFf0f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTTFf0f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTFf0f3 : check 3 TBox336BaseTTFf0f3 LBox336BaseTTFf0f3 RBox336BaseTTFf0f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f3) (wcT 4 RBox336BaseTTFf0f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, false)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0 ih) (AllD.nil 4)))) runBox336BaseTTFf0f3

def LBox336BaseTTFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTTFf1f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTTFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTFf1f3 : check 3 TBox336BaseTTFf1f3 LBox336BaseTTFf1f3 RBox336BaseTTFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf1f3) (wcT 4 RBox336BaseTTFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf1 ih) (AllD.nil 4)))) runBox336BaseTTFf1f3

def LBox336BaseTTFf0f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTTFf0f1f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTTFf0f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTFf0f1f3 : check 3 TBox336BaseTTFf0f1f3 LBox336BaseTTFf0f1f3 RBox336BaseTTFf0f1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f1f3) (wcT 4 RBox336BaseTTFf0f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, false)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0f1 ih) (AllD.nil 4)))) runBox336BaseTTFf0f1f3

def LBox336BaseTTFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTTFf2f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTTFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTTFf2f3 : check 3 TBox336BaseTTFf2f3 LBox336BaseTTFf2f3 RBox336BaseTTFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf2f3) (wcT 4 RBox336BaseTTFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, true)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf2 ih) (AllD.nil 4)))) runBox336BaseTTFf2f3

def LBox336BaseTTFf0f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTTFf0f2f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTTFf0f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTTFf0f2f3 : check 3 TBox336BaseTTFf0f2f3 LBox336BaseTTFf0f2f3 RBox336BaseTTFf0f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f2f3) (wcT 4 RBox336BaseTTFf0f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, false)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0f2 ih) (AllD.nil 4)))) runBox336BaseTTFf0f2f3

def LBox336BaseTTFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTTFf1f2f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTTFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTTFf1f2f3 : check 3 TBox336BaseTTFf1f2f3 LBox336BaseTTFf1f2f3 RBox336BaseTTFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf1f2f3) (wcT 4 RBox336BaseTTFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, true)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf1f2 ih) (AllD.nil 4)))) runBox336BaseTTFf1f2f3

def LBox336BaseTTFf0f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTTFf0f1f2f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTTFf0f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTTFf0f1f2f3 : check 3 TBox336BaseTTFf0f1f2f3 LBox336BaseTTFf0f1f2f3 RBox336BaseTTFf0f1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTFf0f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTFf0f1f2f3) (wcT 4 RBox336BaseTTFf0f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, false)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTFf0f1f2 ih) (AllD.nil 4)))) runBox336BaseTTFf0f1f2f3

def LBox336BaseTFFf0 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTFFf0 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTFFf0 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf0 : check 3 TBox336BaseTFFf0 LBox336BaseTFFf0 RBox336BaseTFFf0
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 1 true,
    .sem 2 2 [] 1,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 0 false,
    .rw 1 1 false,
    .sem 2 2 [] 1] = true := by
  decide +kernel

theorem tBox336BaseTFFf0 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0) (wcT 4 RBox336BaseTFFf0) :=
  check_sound ih (AllD.cons (x81_entry 0 .box [1] [(3, false), (2, false), (0, true)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t180 ih)) (AllD.nil 4)))) runBox336BaseTFFf0

def LBox336BaseTFFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTFFf1 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTFFf1 : Tbl := [([tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(0, true), (3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(0, true), (3, false), (2, false)]], [tg .box [1] [(0, true), (3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tg .box [1] [(0, true), (3, false), (2, false)]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf1 : check 3 TBox336BaseTFFf1 LBox336BaseTFFf1 RBox336BaseTFFf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 false,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 0 3 true,
    .sem 2 2 [] 0,
    .rw 1 4 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 2 true,
    .rw 0 1 false,
    .rw 0 0 true,
    .sem 1 2 [] 0,
    .rw 1 3 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf1) (wcT 4 RBox336BaseTFFf1) :=
  check_sound ih (AllD.cons (g_entry .box [1] [(3, false), (2, false), (0, true)] [(0, true), (3, false), (2, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [2, 1, 0] (by decide +kernel) (t156f1f2 ih)) (AllD.cons (g_entry .box [1] [(0, true), (3, false), (2, false)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t180 ih)) (AllD.nil 4)))))) runBox336BaseTFFf1

def LBox336BaseTFFf0f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTFFf0f1 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTFFf0f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf0f1 : check 3 TBox336BaseTFFf0f1 LBox336BaseTFFf0f1 RBox336BaseTFFf0f1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [] 0,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f1) (wcT 4 RBox336BaseTFFf0f1) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t156f1f2f3 ih)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0 ih) (AllD.nil 4)))) runBox336BaseTFFf0f1

def LBox336BaseTFFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTFFf2 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTFFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf2 : check 3 TBox336BaseTFFf2 LBox336BaseTFFf2 RBox336BaseTFFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf2) (wcT 4 RBox336BaseTFFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, false), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t180 ih)) (AllD.nil 4)))) runBox336BaseTFFf2

def LBox336BaseTFFf0f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTFFf0f2 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTFFf0f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf0f2 : check 3 TBox336BaseTFFf0f2 LBox336BaseTFFf0f2 RBox336BaseTFFf0f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f2) (wcT 4 RBox336BaseTFFf0f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, false), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0 ih) (AllD.nil 4)))) runBox336BaseTFFf0f2

def LBox336BaseTFFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTFFf1f2 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTFFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFFf1f2 : check 3 TBox336BaseTFFf1f2 LBox336BaseTFFf1f2 RBox336BaseTFFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf1f2) (wcT 4 RBox336BaseTFFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, false), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf1 ih) (AllD.nil 4)))) runBox336BaseTFFf1f2

def LBox336BaseTFFf0f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTFFf0f1f2 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTFFf0f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFFf0f1f2 : check 3 TBox336BaseTFFf0f1f2 LBox336BaseTFFf0f1f2 RBox336BaseTFFf0f1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f1f2) (wcT 4 RBox336BaseTFFf0f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, false), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0f1 ih) (AllD.nil 4)))) runBox336BaseTFFf0f1f2

def LBox336BaseTFFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTFFf3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTFFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf3 : check 3 TBox336BaseTFFf3 LBox336BaseTFFf3 RBox336BaseTFFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf3) (wcT 4 RBox336BaseTFFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, true)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t180 ih)) (AllD.nil 4)))) runBox336BaseTFFf3

def LBox336BaseTFFf0f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTFFf0f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTFFf0f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTFFf0f3 : check 3 TBox336BaseTFFf0f3 LBox336BaseTFFf0f3 RBox336BaseTFFf0f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f3) (wcT 4 RBox336BaseTFFf0f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, false)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0 ih) (AllD.nil 4)))) runBox336BaseTFFf0f3

def LBox336BaseTFFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTFFf1f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTFFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFFf1f3 : check 3 TBox336BaseTFFf1f3 LBox336BaseTFFf1f3 RBox336BaseTFFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf1f3) (wcT 4 RBox336BaseTFFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, true)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf1 ih) (AllD.nil 4)))) runBox336BaseTFFf1f3

def LBox336BaseTFFf0f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTFFf0f1f3 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTFFf0f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]], [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTFFf0f1f3 : check 3 TBox336BaseTFFf0f1f3 LBox336BaseTFFf0f1f3 RBox336BaseTFFf0f1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f1f3) (wcT 4 RBox336BaseTFFf0f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, false), (0, false)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0f1 ih) (AllD.nil 4)))) runBox336BaseTFFf0f1f3

def LBox336BaseTFFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTFFf2f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTFFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTFFf2f3 : check 3 TBox336BaseTFFf2f3 LBox336BaseTFFf2f3 RBox336BaseTFFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf2f3) (wcT 4 RBox336BaseTFFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf2 ih) (AllD.nil 4)))) runBox336BaseTFFf2f3

def LBox336BaseTFFf0f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTFFf0f2f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTFFf0f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTFFf0f2f3 : check 3 TBox336BaseTFFf0f2f3 LBox336BaseTFFf0f2f3 RBox336BaseTFFf0f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f2f3) (wcT 4 RBox336BaseTFFf0f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, false)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0f2 ih) (AllD.nil 4)))) runBox336BaseTFFf0f2f3

def LBox336BaseTFFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTFFf1f2f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTFFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTFFf1f2f3 : check 3 TBox336BaseTFFf1f2f3 LBox336BaseTFFf1f2f3 RBox336BaseTFFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf1f2f3) (wcT 4 RBox336BaseTFFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf1f2 ih) (AllD.nil 4)))) runBox336BaseTFFf1f2f3

def LBox336BaseTFFf0f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTFFf0f1f2f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTFFf0f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]], [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTFFf0f1f2f3 : check 3 TBox336BaseTFFf0f1f2f3 LBox336BaseTFFf0f1f2f3 RBox336BaseTFFf0f1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTFFf0f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTFFf0f1f2f3) (wcT 4 RBox336BaseTFFf0f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, false)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTFFf0f1f2 ih) (AllD.nil 4)))) runBox336BaseTFFf0f1f2f3

def LBox336BaseTTTf0 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTTTf0 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def TBox336BaseTTTf0 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]], [tg .box [1] [(3, true), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf0 : check 3 TBox336BaseTTTf0 LBox336BaseTTTf0 RBox336BaseTTTf0
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 1 true,
    .sem 2 2 [] 1,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .rw 0 0 false,
    .rw 1 1 false,
    .sem 2 2 [] 1] = true := by
  decide +kernel

theorem tBox336BaseTTTf0 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0) (wcT 4 RBox336BaseTTTf0) :=
  check_sound ih (AllD.cons (x81_entry 0 .box [1] [(3, true), (2, true), (0, true)] [(3, true), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (t156 ih) (AllD.cons (tBox336BaseTTT ih) (AllD.nil 4)))) runBox336BaseTTTf0

def LBox336BaseTTTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]]

def RBox336BaseTTTf1 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTTTf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf1 : check 3 TBox336BaseTTTf1 LBox336BaseTTTf1 RBox336BaseTTTf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [] 0,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf1) (wcT 4 RBox336BaseTTTf1) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t156 ih)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTT ih) (AllD.nil 4)))) runBox336BaseTTTf1

def LBox336BaseTTTf0f1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]]

def RBox336BaseTTTf0f1 : List Tk := [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TBox336BaseTTTf0f1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf0f1 : check 3 TBox336BaseTTTf0f1 LBox336BaseTTTf0f1 RBox336BaseTTTf0f1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [] 0,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f1) (wcT 4 RBox336BaseTTTf0f1) :=
  check_sound ih (AllD.cons (rel_entry (havail4b ih) [0] (by decide +kernel) (t156f1 ih)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0 ih) (AllD.nil 4)))) runBox336BaseTTTf0f1

def LBox336BaseTTTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTTTf2 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTTTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf2 : check 3 TBox336BaseTTTf2 LBox336BaseTTTf2 RBox336BaseTTTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf2) (wcT 4 RBox336BaseTTTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, true), (0, true)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTT ih) (AllD.nil 4)))) runBox336BaseTTTf2

def LBox336BaseTTTf0f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTTTf0f2 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def TBox336BaseTTTf0f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf0f2 : check 3 TBox336BaseTTTf0f2 LBox336BaseTTTf0f2 RBox336BaseTTTf0f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f2) (wcT 4 RBox336BaseTTTf0f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, true), (0, false)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0 ih) (AllD.nil 4)))) runBox336BaseTTTf0f2

def LBox336BaseTTTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]]

def RBox336BaseTTTf1f2 : List Tk := [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTTTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTTf1f2 : check 3 TBox336BaseTTTf1f2 LBox336BaseTTTf1f2 RBox336BaseTTTf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf1f2) (wcT 4 RBox336BaseTTTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, true), (0, true)] [(3, true), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf1 ih) (AllD.nil 4)))) runBox336BaseTTTf1f2

def LBox336BaseTTTf0f1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]]

def RBox336BaseTTTf0f1f2 : List Tk := [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TBox336BaseTTTf0f1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, true), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTTf0f1f2 : check 3 TBox336BaseTTTf0f1f2 LBox336BaseTTTf0f1f2 RBox336BaseTTTf0f1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f1f2) (wcT 4 RBox336BaseTTTf0f1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, true), (2, true), (0, false)] [(3, true), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0f1 ih) (AllD.nil 4)))) runBox336BaseTTTf0f1f2

def LBox336BaseTTTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTTTf3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTTTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf3 : check 3 TBox336BaseTTTf3 LBox336BaseTTTf3 RBox336BaseTTTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf3) (wcT 4 RBox336BaseTTTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTT ih) (AllD.nil 4)))) runBox336BaseTTTf3

def LBox336BaseTTTf0f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTTTf0f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def TBox336BaseTTTf0f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runBox336BaseTTTf0f3 : check 3 TBox336BaseTTTf0f3 LBox336BaseTTTf0f3 RBox336BaseTTTf0f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f3) (wcT 4 RBox336BaseTTTf0f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0 ih) (AllD.nil 4)))) runBox336BaseTTTf0f3

def LBox336BaseTTTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, true)]]

def RBox336BaseTTTf1f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTTTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, true)]], [tg .box [1] [(3, true), (2, true), (0, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTTf1f3 : check 3 TBox336BaseTTTf1f3 LBox336BaseTTTf1f3 RBox336BaseTTTf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf1f3) (wcT 4 RBox336BaseTTTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf1 ih) (AllD.nil 4)))) runBox336BaseTTTf1f3

def LBox336BaseTTTf0f1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .box [1] [(3, false), (2, true), (0, false)]]

def RBox336BaseTTTf0f1f3 : List Tk := [tg .box [1] [(3, false), (2, true), (0, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TBox336BaseTTTf0f1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, true), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, true), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .box [1] [(3, true), (2, true), (0, false)]], [tg .box [1] [(3, true), (2, true), (0, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runBox336BaseTTTf0f1f3 : check 3 TBox336BaseTTTf0f1f3 LBox336BaseTTTf0f1f3 RBox336BaseTTTf0f1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f1f3) (wcT 4 RBox336BaseTTTf0f1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, true), (0, false)] [(3, false), (2, true), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0f1 ih) (AllD.nil 4)))) runBox336BaseTTTf0f1f3

def LBox336BaseTTTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTTTf2f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTTTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTTTf2f3 : check 3 TBox336BaseTTTf2f3 LBox336BaseTTTf2f3 RBox336BaseTTTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf2f3) (wcT 4 RBox336BaseTTTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, true)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf2 ih) (AllD.nil 4)))) runBox336BaseTTTf2f3

def LBox336BaseTTTf0f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTTTf0f2f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def TBox336BaseTTTf0f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runBox336BaseTTTf0f2f3 : check 3 TBox336BaseTTTf0f2f3 LBox336BaseTTTf0f2f3 RBox336BaseTTTf0f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f2f3) (wcT 4 RBox336BaseTTTf0f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, false)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0f2 ih) (AllD.nil 4)))) runBox336BaseTTTf0f2f3

def LBox336BaseTTTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, false), (2, false), (0, true)]]

def RBox336BaseTTTf1f2f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTTTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, false), (0, true)]], [tg .box [1] [(3, true), (2, false), (0, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTTTf1f2f3 : check 3 TBox336BaseTTTf1f2f3 LBox336BaseTTTf1f2f3 RBox336BaseTTTf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf1f2f3) (wcT 4 RBox336BaseTTTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, true)] [(3, false), (2, false), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf1f2 ih) (AllD.nil 4)))) runBox336BaseTTTf1f2f3

def LBox336BaseTTTf0f1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .box [1] [(3, false), (2, false), (0, false)]]

def RBox336BaseTTTf0f1f2f3 : List Tk := [tg .box [1] [(3, false), (2, false), (0, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TBox336BaseTTTf0f1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, true), (2, false), (0, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, false), (2, false), (0, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .box [1] [(3, true), (2, false), (0, false)]], [tg .box [1] [(3, true), (2, false), (0, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runBox336BaseTTTf0f1f2f3 : check 3 TBox336BaseTTTf0f1f2f3 LBox336BaseTTTf0f1f2f3 RBox336BaseTTTf0f1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tBox336BaseTTTf0f1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LBox336BaseTTTf0f1f2f3) (wcT 4 RBox336BaseTTTf0f1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, true), (2, false), (0, false)] [(3, false), (2, false), (0, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tBox336BaseTTTf0f1f2 ih) (AllD.nil 4)))) runBox336BaseTTTf0f1f2f3

end QCert.RealCliffordCH.Sec8.D.W4Low
