/- Three-wire base cases of (335), (336), and (340). -/
import QCert.RealCliffordCH.Sec8.D.W3.Tokens

namespace QCert.RealCliffordCH.Sec8.D.Low3Hg
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
def LLowHg3_337FFT : List Tk := [tg .box [0] [(2, false), (1, false)], tg .hg [0, 1] [(2, true)]]

def RLowHg3_337FFT : List Tk := [tg .hg [0, 1] [(2, true)], tg .box [0] [(2, false), (1, false)]]

def TLowHg3_337FFT : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tK 1], [tg .hg [0, 1] [(2, true)]])]

theorem runLowHg3_337FFT : check 2 TLowHg3_337FFT LLowHg3_337FFT RLowHg3_337FFT
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .rw 13 1 true,
    .sem 13 1 [tK 1] 0,
    .sem 0 14 [tK 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false,
    .sem 0 1 [tK 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLowHg3_337FFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg3_337FFT) (wcT 3 RLowHg3_337FFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLowHg3_337FFT

def LLowHg3_337FFTf2 : List Tk := [tg .box [0] [(2, true), (1, false)], tg .hg [0, 1] [(2, false)]]

def RLowHg3_337FFTf2 : List Tk := [tg .hg [0, 1] [(2, false)], tg .box [0] [(2, true), (1, false)]]

def TLowHg3_337FFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(2, true), (1, false)]]),
  ([tg .box [0] [(2, false), (1, false)], tg .hg [0, 1] [(2, true)]], [tg .hg [0, 1] [(2, true)], tg .box [0] [(2, false), (1, false)]])]

theorem runLowHg3_337FFTf2 : check 2 TLowHg3_337FFTf2 LLowHg3_337FFTf2 RLowHg3_337FFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tLowHg3_337FFTf2 (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg3_337FFTf2) (wcT 3 RLowHg3_337FFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(2, true)] [(2, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(2, false), (1, false)] [(2, true), (1, false)] (by decide +kernel)) (AllD.cons (tLowHg3_337FFT ih) (AllD.nil 3)))) runLowHg3_337FFTf2

def LLowHg3_337FTF : List Tk := [tg .box [0] [(2, true), (1, false)], tg .hg [0, 1] [(2, false)]]

def RLowHg3_337FTF : List Tk := [tg .hg [0, 1] [(2, false)], tg .box [0] [(2, true), (1, false)]]

def TLowHg3_337FTF : Tbl := [([tg .box [0] [(2, true), (1, false)], tg .hg [0, 1] [(2, false)]], [tg .hg [0, 1] [(2, false)], tg .box [0] [(2, true), (1, false)]])]

theorem runLowHg3_337FTF : check 2 TLowHg3_337FTF LLowHg3_337FTF RLowHg3_337FTF
    [.rw 0 0 false] = true := by
  decide +kernel

theorem tLowHg3_337FTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg3_337FTF) (wcT 3 RLowHg3_337FTF) :=
  check_sound ih (AllD.cons (tLowHg3_337FFTf2 ih) (AllD.nil 3)) runLowHg3_337FTF

def LLowHg3_337TFT : List Tk := [tg .box [0] [(2, false), (1, true)], tg .hg [0, 1] [(2, true)]]

def RLowHg3_337TFT : List Tk := [tg .hg [0, 1] [(2, true)], tg .box [0] [(2, false), (1, true)]]

def TLowHg3_337TFT : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tK 1], [tg .hg [0, 1] [(2, true)]])]

theorem runLowHg3_337TFT : check 2 TLowHg3_337TFT LLowHg3_337TFT RLowHg3_337TFT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 7 1 [tK 1] 0,
    .sem 0 8 [tK 1, tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false,
    .sem 0 1 [tK 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLowHg3_337TFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg3_337TFT) (wcT 3 RLowHg3_337TFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLowHg3_337TFT

def LLowHg3_337TFTf2 : List Tk := [tg .box [0] [(2, true), (1, true)], tg .hg [0, 1] [(2, false)]]

def RLowHg3_337TFTf2 : List Tk := [tg .hg [0, 1] [(2, false)], tg .box [0] [(2, true), (1, true)]]

def TLowHg3_337TFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(2, true), (1, true)]]),
  ([tg .box [0] [(2, false), (1, true)], tg .hg [0, 1] [(2, true)]], [tg .hg [0, 1] [(2, true)], tg .box [0] [(2, false), (1, true)]])]

theorem runLowHg3_337TFTf2 : check 2 TLowHg3_337TFTf2 LLowHg3_337TFTf2 RLowHg3_337TFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tLowHg3_337TFTf2 (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg3_337TFTf2) (wcT 3 RLowHg3_337TFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(2, true)] [(2, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(2, false), (1, true)] [(2, true), (1, true)] (by decide +kernel)) (AllD.cons (tLowHg3_337TFT ih) (AllD.nil 3)))) runLowHg3_337TFTf2

def LLowHg3_337TTF : List Tk := [tg .box [0] [(2, true), (1, true)], tg .hg [0, 1] [(2, false)]]

def RLowHg3_337TTF : List Tk := [tg .hg [0, 1] [(2, false)], tg .box [0] [(2, true), (1, true)]]

def TLowHg3_337TTF : Tbl := [([tg .box [0] [(2, true), (1, true)], tg .hg [0, 1] [(2, false)]], [tg .hg [0, 1] [(2, false)], tg .box [0] [(2, true), (1, true)]])]

theorem runLowHg3_337TTF : check 2 TLowHg3_337TTF LLowHg3_337TTF RLowHg3_337TTF
    [.rw 0 0 false] = true := by
  decide +kernel

theorem tLowHg3_337TTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLowHg3_337TTF) (wcT 3 RLowHg3_337TTF) :=
  check_sound ih (AllD.cons (tLowHg3_337TFTf2 ih) (AllD.nil 3)) runLowHg3_337TTF

end QCert.RealCliffordCH.Sec8.D.Low3Hg
