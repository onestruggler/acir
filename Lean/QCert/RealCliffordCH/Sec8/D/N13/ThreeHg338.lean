/- Three-wire base cases of (335), (336), and (340). -/
import QCert.RealCliffordCH.Sec8.D.W3.Tokens

namespace QCert.RealCliffordCH.Sec8.D.Low3Hg338
open Circuit WE WS
open Eng (L)
abbrev tH (j : Nat) : Tk := Tk.s (L.H j)
abbrev tZ (j : Nat) : Tk := Tk.s (L.Z j)
abbrev tC (j : Nat) : Tk := Tk.s (L.C j)
abbrev tK (j : Nat) : Tk := Tk.s (L.K j)
abbrev tS (j : Nat) : Tk := Tk.s (L.S j)
abbrev tg (Kd : Kind) (tg : List Nat) (cs : List (Nat × Bool)) : Tk := Tk.g Kd tg cs
abbrev tp (m : Nat) (w : List L) (ps : List Nat) : Tk := Tk.p m w ps
private theorem havailNone : ∀ (K : Kind) (k : Nat), false = true → Net.CanonSym K k := by
  intro K k h
  cases h
def LLowHg338FFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .hg [1, 0] [(2, false)]]

def RLowHg338FFF : List Tk := [tg .hg [1, 0] [(2, false)], tg .box [0] [(2, false), (1, false)]]

def TLowHg338FFF : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2], [tg .hg [1, 0] [(2, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]])]

theorem runLowHg338FFF : check 2 TLowHg338FFF LLowHg338FFF RLowHg338FFF
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .sem 0 13 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .rw 3 1 true,
    .sem 7 1 [tK 1] 0,
    .sem 7 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 6 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 3 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .swp 2 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) true,
    .swp 5 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]) true,
    .sem 4 2 [] 0,
    .sem 3 1 [tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2] 0,
    .sem 11 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sem 10 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]] 0,
    .sem 3 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 4 0 [tS 1, tS 1] 0,
    .swp 5 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) false,
    .swp 2 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]) false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tZ 2] 1,
    .sem 0 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 0 1 [tH 2, tZ 2, tH 2, tp 2 [L.K 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 4 1 [tK 1] 0,
    .sem 4 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 3 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338FFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338FFF) (wcT 3 RLowHg338FFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13f1 ih)) (AllD.nil 3)))) runLowHg338FFF

def LLowHg338FFT : List Tk := [tg .box [0] [(2, false), (1, false)], tg .hg [1, 0] [(2, true)]]

def RLowHg338FFT : List Tk := [tg .hg [1, 0] [(2, true)], tg .box [0] [(2, false), (1, false)]]

def TLowHg338FFT : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tS 0, tK 1, tS 0], [tg .hg [1, 0] [(2, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLowHg338FFT : check 2 TLowHg338FFT LLowHg338FFT RLowHg338FFT
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .sem 0 13 [tp 2 [L.C 0] [1, 2], tZ 1, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .rw 4 1 true,
    .sem 5 1 [tK 1] 0,
    .sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 3 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) true,
    .swp 6 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 5 2 [] 0,
    .sem 4 1 [tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2] 0,
    .sem 12 1 [tK 0] 2,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]] 0,
    .sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 5 0 [tS 1, tS 1] 0,
    .swp 6 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) false,
    .swp 3 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 2 2 [tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tK 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 4 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338FFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338FFT) (wcT 3 RLowHg338FFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13 ih)) (AllD.nil 3)))) runLowHg338FFT

def LLowHg338FTF : List Tk := [tg .box [0] [(2, true), (1, false)], tg .hg [1, 0] [(2, false)]]

def RLowHg338FTF : List Tk := [tg .hg [1, 0] [(2, false)], tg .box [0] [(2, true), (1, false)]]

def TLowHg338FTF : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2], [tg .hg [1, 0] [(2, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]])]

theorem runLowHg338FTF : check 2 TLowHg338FTF LLowHg338FTF RLowHg338FTF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tZ 1, tZ 2] 0,
    .rw 3 1 true,
    .sem 7 1 [tK 1] 0,
    .sem 7 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 6 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 3 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .sem 2 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tZ 2] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sem 9 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]) false,
    .sem 0 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 0 1 [tH 2, tZ 2, tH 2, tp 2 [L.K 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 4 1 [tK 1] 0,
    .sem 4 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 3 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338FTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338FTF) (wcT 3 RLowHg338FTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13f1 ih)) (AllD.nil 3)))) runLowHg338FTF

def LLowHg338FTT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .hg [1, 0] [(2, true)]]

def RLowHg338FTT : List Tk := [tg .hg [1, 0] [(2, true)], tg .box [0] [(2, true), (1, false)]]

def TLowHg338FTT : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tS 0, tK 1, tS 0], [tg .hg [1, 0] [(2, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLowHg338FTT : check 2 TLowHg338FTT LLowHg338FTT RLowHg338FTT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 2] 0,
    .rw 2 1 true,
    .sem 3 1 [tK 1] 0,
    .sem 3 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 2 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 1 2 [tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338FTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338FTT) (wcT 3 RLowHg338FTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13 ih)) (AllD.nil 3)))) runLowHg338FTT

def LLowHg338TFF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .hg [1, 0] [(2, false)]]

def RLowHg338TFF : List Tk := [tg .hg [1, 0] [(2, false)], tg .box [0] [(2, false), (1, true)]]

def TLowHg338TFF : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2], [tg .hg [1, 0] [(2, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]])]

theorem runLowHg338TFF : check 2 TLowHg338TFF LLowHg338TFF RLowHg338TFF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .rw 1 1 true,
    .sem 5 1 [tK 1] 0,
    .sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 1 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .sem 0 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 0 1 [tH 2, tZ 2, tH 2, tp 2 [L.K 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 4 1 [tK 1] 0,
    .sem 4 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338TFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338TFF) (wcT 3 RLowHg338TFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13f1 ih)) (AllD.nil 3)))) runLowHg338TFF

def LLowHg338TFT : List Tk := [tg .box [0] [(2, false), (1, true)], tg .hg [1, 0] [(2, true)]]

def RLowHg338TFT : List Tk := [tg .hg [1, 0] [(2, true)], tg .box [0] [(2, false), (1, true)]]

def TLowHg338TFT : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tS 0, tK 1, tS 0], [tg .hg [1, 0] [(2, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLowHg338TFT : check 2 TLowHg338TFT LLowHg338TFT RLowHg338TFT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 1] 0,
    .rw 2 1 true,
    .sem 3 1 [tK 1] 0,
    .sem 3 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 2 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tK 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338TFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338TFT) (wcT 3 RLowHg338TFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13 ih)) (AllD.nil 3)))) runLowHg338TFT

def LLowHg338TTF : List Tk := [tg .box [0] [(2, true), (1, true)], tg .hg [1, 0] [(2, false)]]

def RLowHg338TTF : List Tk := [tg .hg [1, 0] [(2, false)], tg .box [0] [(2, true), (1, true)]]

def TLowHg338TTF : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2], [tg .hg [1, 0] [(2, false)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]])]

theorem runLowHg338TTF : check 2 TLowHg338TTF LLowHg338TTF RLowHg338TTF
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .sem 0 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tZ 1] 0,
    .rw 2 1 true,
    .sem 6 1 [tK 1] 0,
    .sem 6 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 5 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 2 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sem 9 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]) false,
    .sem 0 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 0 1 [tH 2, tZ 2, tH 2, tp 2 [L.K 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 4 1 [tK 1] 0,
    .sem 4 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338TTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338TTF) (wcT 3 RLowHg338TTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13f1 ih)) (AllD.nil 3)))) runLowHg338TTF

def LLowHg338TTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .hg [1, 0] [(2, true)]]

def RLowHg338TTT : List Tk := [tg .hg [1, 0] [(2, true)], tg .box [0] [(2, true), (1, true)]]

def TLowHg338TTT : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tS 0, tK 1, tS 0], [tg .hg [1, 0] [(2, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLowHg338TTT : check 2 TLowHg338TTT LLowHg338TTT RLowHg338TTT
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .sem 0 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 1 1 true,
    .sem 2 1 [tK 1] 0,
    .sem 2 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLowHg338TTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg338TTT) (wcT 3 RLowHg338TTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te13 ih)) (AllD.nil 3)))) runLowHg338TTT

end QCert.RealCliffordCH.Sec8.D.Low3Hg338
