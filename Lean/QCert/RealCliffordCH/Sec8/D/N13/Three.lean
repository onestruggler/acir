/- Three-wire base cases of (335), (336), and (340). -/
import QCert.RealCliffordCH.Sec8.D.W3.Tokens

namespace QCert.RealCliffordCH.Sec8.D.Low3
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
def LLow3_335FFFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, false), (1, false)]]

def RLow3_335FFFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, false), (1, false)]]

def TLow3_335FFFF : Tbl := []

theorem runLow3_335FFFF : check 2 TLow3_335FFFF LLow3_335FFFF RLow3_335FFFF
    [] = true := by
  decide +kernel

theorem tLow3_335FFFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FFFF) (wcT 3 RLow3_335FFFF) :=
  check_sound ih (AllD.nil 3) runLow3_335FFFF

def LLow3_335FFFT : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, true), (1, false)]]

def RLow3_335FFFT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, false), (1, false)]]

def TLow3_335FFFT : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]])]

theorem runLow3_335FFFT : check 2 TLow3_335FFFT LLow3_335FFFT RLow3_335FFFT
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .rw 13 1 true,
    .sem 16 1 [tC 1] 0,
    .sem 3 17 [tC 1, tH 1, tZ 1, tH 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 13 1 [tC 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335FFFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FFFT) (wcT 3 RLow3_335FFFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335FFFT

def LLow3_335FFTF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, false), (1, true)]]

def RLow3_335FFTF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, false), (1, false)]]

def TLow3_335FFTF : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]])]

theorem runLow3_335FFTF : check 2 TLow3_335FFTF LLow3_335FFTF RLow3_335FFTF
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .rw 13 1 true,
    .sem 16 1 [tC 1] 0,
    .sem 12 2 [] 0,
    .sem 11 2 [] 0,
    .sem 10 2 [] 0,
    .sem 0 11 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 13 1 [tC 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335FFTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FFTF) (wcT 3 RLow3_335FFTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335FFTF

def LLow3_335FFTT : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, true), (1, true)]]

def RLow3_335FFTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, false), (1, false)]]

def TLow3_335FFTT : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tC 1], [tg .box [0] [(2, true), (1, true)]])]

theorem runLow3_335FFTT : check 2 TLow3_335FFTT LLow3_335FFTT RLow3_335FFTT
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .rw 13 1 true,
    .sem 13 1 [tC 1] 0,
    .sem 0 14 [tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false,
    .sem 0 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335FFTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FFTT) (wcT 3 RLow3_335FFTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335FFTT

def LLow3_335FTFF : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, false), (1, false)]]

def RLow3_335FTFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, true), (1, false)]]

def TLow3_335FTFF : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]])]

theorem runLow3_335FTFF : check 2 TLow3_335FTFF LLow3_335FTFF RLow3_335FTFF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 13 1 [tC 1] 0,
    .sem 6 2 [] 0,
    .sem 5 2 [] 0,
    .sem 4 2 [] 0,
    .sem 3 11 [tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 16 1 [tC 1] 0,
    .rw 13 0 false,
    .sem 6 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335FTFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FTFF) (wcT 3 RLow3_335FTFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335FTFF

def LLow3_335FTFT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, true), (1, false)]]

def RLow3_335FTFT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, true), (1, false)]]

def TLow3_335FTFT : Tbl := []

theorem runLow3_335FTFT : check 2 TLow3_335FTFT LLow3_335FTFT RLow3_335FTFT
    [] = true := by
  decide +kernel

theorem tLow3_335FTFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FTFT) (wcT 3 RLow3_335FTFT) :=
  check_sound ih (AllD.nil 3) runLow3_335FTFT

def LLow3_335FTTF : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, false), (1, true)]]

def RLow3_335FTTF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, true), (1, false)]]

def TLow3_335FTTF : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]])]

theorem runLow3_335FTTF : check 2 TLow3_335FTTF LLow3_335FTTF RLow3_335FTTF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 10 1 [tC 1] 0,
    .sem 0 14 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 10 1 [tC 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335FTTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FTTF) (wcT 3 RLow3_335FTTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335FTTF

def LLow3_335FTTT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, true), (1, true)]]

def RLow3_335FTTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, true), (1, false)]]

def TLow3_335FTTT : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tC 1], [tg .box [0] [(2, true), (1, true)]])]

theorem runLow3_335FTTT : check 2 TLow3_335FTTT LLow3_335FTTT RLow3_335FTTT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 7 1 [tC 1] 0,
    .sem 0 8 [tC 1, tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false,
    .sem 0 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335FTTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335FTTT) (wcT 3 RLow3_335FTTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335FTTT

def LLow3_335TFFF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, false), (1, false)]]

def RLow3_335TFFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, false), (1, true)]]

def TLow3_335TFFF : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]])]

theorem runLow3_335TFFF : check 2 TLow3_335TFFF LLow3_335TFFF RLow3_335TFFF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 13 1 [tC 1] 0,
    .sem 3 14 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tH 2, tZ 2, tH 2, tC 1] 0,
    .sem 16 1 [tC 1] 0,
    .rw 13 0 false,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 0,
    .sw 1,
    .sw 2,
    .sem 6 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335TFFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TFFF) (wcT 3 RLow3_335TFFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335TFFF

def LLow3_335TFFT : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, true), (1, false)]]

def RLow3_335TFFT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, false), (1, true)]]

def TLow3_335TFFT : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]])]

theorem runLow3_335TFFT : check 2 TLow3_335TFFT LLow3_335TFFT RLow3_335TFFT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 10 1 [tC 1] 0,
    .sem 0 14 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 10 1 [tC 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335TFFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TFFT) (wcT 3 RLow3_335TFFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335TFFT

def LLow3_335TFTF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, false), (1, true)]]

def RLow3_335TFTF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, false), (1, true)]]

def TLow3_335TFTF : Tbl := []

theorem runLow3_335TFTF : check 2 TLow3_335TFTF LLow3_335TFTF RLow3_335TFTF
    [] = true := by
  decide +kernel

theorem tLow3_335TFTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TFTF) (wcT 3 RLow3_335TFTF) :=
  check_sound ih (AllD.nil 3) runLow3_335TFTF

def LLow3_335TFTT : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, true), (1, true)]]

def RLow3_335TFTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, false), (1, true)]]

def TLow3_335TFTT : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tC 1], [tg .box [0] [(2, true), (1, true)]])]

theorem runLow3_335TFTT : check 2 TLow3_335TFTT LLow3_335TFTT RLow3_335TFTT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .rw 7 1 true,
    .sem 7 1 [tC 1] 0,
    .sem 0 8 [tC 1, tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false,
    .sem 0 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335TFTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TFTT) (wcT 3 RLow3_335TFTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335TFTT

def LLow3_335TTFF : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, false), (1, false)]]

def RLow3_335TTFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [0] [(2, true), (1, true)]]

def TLow3_335TTFF : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]])]

theorem runLow3_335TTFF : check 2 TLow3_335TTFF LLow3_335TTFF RLow3_335TTFF
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .rw 1 1 true,
    .sem 7 1 [tC 1] 0,
    .sem 0 14 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1] 0,
    .sem 13 1 [tC 1] 0,
    .rw 13 0 false,
    .sem 6 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335TTFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TTFF) (wcT 3 RLow3_335TTFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335TTFF

def LLow3_335TTFT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, true), (1, false)]]

def RLow3_335TTFT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [0] [(2, true), (1, true)]]

def TLow3_335TTFT : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]])]

theorem runLow3_335TTFT : check 2 TLow3_335TTFT LLow3_335TTFT RLow3_335TTFT
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .rw 1 1 true,
    .sem 4 1 [tC 1] 0,
    .sem 0 8 [tH 1, tC 1, tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1] 0,
    .sem 1 7 [tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1, tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335TTFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TTFT) (wcT 3 RLow3_335TTFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335TTFT

def LLow3_335TTTF : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, false), (1, true)]]

def RLow3_335TTTF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [0] [(2, true), (1, true)]]

def TLow3_335TTTF : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]])]

theorem runLow3_335TTTF : check 2 TLow3_335TTTF LLow3_335TTTF RLow3_335TTTF
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .rw 1 1 true,
    .sem 4 1 [tC 1] 0,
    .sem 0 8 [tH 2, tC 1, tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2] 0,
    .sem 1 7 [tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2, tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tC 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_335TTTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TTTF) (wcT 3 RLow3_335TTTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_335TTTF

def LLow3_335TTTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, true), (1, true)]]

def RLow3_335TTTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [0] [(2, true), (1, true)]]

def TLow3_335TTTT : Tbl := []

theorem runLow3_335TTTT : check 2 TLow3_335TTTT LLow3_335TTTT RLow3_335TTTT
    [] = true := by
  decide +kernel

theorem tLow3_335TTTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_335TTTT) (wcT 3 RLow3_335TTTT) :=
  check_sound ih (AllD.nil 3) runLow3_335TTTT

def LLow3_336FFFF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [1] [(2, false), (0, false)]]

def RLow3_336FFFF : List Tk := [tg .box [1] [(2, false), (0, false)], tg .box [0] [(2, false), (1, false)]]

def TLow3_336FFFF : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FFFF : check 2 TLow3_336FFFF LLow3_336FFFF RLow3_336FFFF
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .sem 0 13 [tp 2 [L.C 0] [1, 2], tZ 1, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .rw 4 1 true,
    .sem 11 1 [tC 1] 0,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 10 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 13 [tp 2 [L.C 0] [0, 2], tZ 0, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .swp 3 0 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) true,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 5 2 [] 2,
    .sem 4 1 [tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0] 1,
    .sem 12 1 [tC 1] 0,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 4 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 5 0 [tS 0, tS 0] 2,
    .swp 6 0 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) false,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 2 [tZ 0, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 2,
    .sem 2 2 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sw 3,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sw 2,
    .sw 3,
    .sem 4 2 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0], tZ 1] 2,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 2 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 1 [tC 1] 0,
    .sem 4 1 [tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0] 1,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 7 1 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 2,
    .sem 0 4 [tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2] 1,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 1 [tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 4 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FFFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FFFF) (wcT 3 RLow3_336FFFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FFFF

def LLow3_336FFFT : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [1] [(2, true), (0, false)]]

def RLow3_336FFFT : List Tk := [tg .box [1] [(2, true), (0, false)], tg .box [0] [(2, false), (1, false)]]

def TLow3_336FFFT : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tH 0, tZ 0, tH 0, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0], [tg .box [1] [(2, true), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FFFT : check 2 TLow3_336FFFT LLow3_336FFFT RLow3_336FFFT
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .sem 0 13 [tp 2 [L.C 0] [1, 2], tZ 1, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .rw 4 1 true,
    .sem 8 1 [tC 1] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 7 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 7 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .swp 3 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) true,
    .swp 6 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 5 2 [] 0,
    .sem 4 1 [tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2] 0,
    .sem 12 1 [tC 0] 2,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]] 0,
    .sem 4 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 5 0 [tS 1, tS 1] 0,
    .swp 6 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) false,
    .swp 3 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 2 [tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .sem 2 2 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sw 2,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 0 2 [tH 0, tZ 0, tH 0, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 4 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FFFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FFFT) (wcT 3 RLow3_336FFFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FFFT

def LLow3_336FFTF : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [1] [(2, false), (0, true)]]

def RLow3_336FFTF : List Tk := [tg .box [1] [(2, false), (0, true)], tg .box [0] [(2, false), (1, false)]]

def TLow3_336FFTF : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FFTF : check 2 TLow3_336FFTF LLow3_336FFTF RLow3_336FFTF
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .sem 0 13 [tp 2 [L.C 0] [1, 2], tZ 1, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .rw 4 1 true,
    .sem 8 1 [tC 1] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 7 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 7 [tp 2 [L.C 0] [0, 2], tZ 0] 1,
    .swp 3 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) true,
    .swp 6 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 5 2 [] 0,
    .sem 4 1 [tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2] 0,
    .sem 12 1 [tC 0] 2,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]] 0,
    .sem 4 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 5 0 [tS 1, tS 1] 0,
    .swp 6 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) false,
    .swp 3 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 2 [tZ 0, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 2,
    .sem 2 2 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sw 3,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sw 2,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 0 2 [tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 4 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FFTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FFTF) (wcT 3 RLow3_336FFTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FFTF

def LLow3_336FFTT : List Tk := [tg .box [0] [(2, false), (1, false)], tg .box [1] [(2, true), (0, true)]]

def RLow3_336FFTT : List Tk := [tg .box [1] [(2, true), (0, true)], tg .box [0] [(2, false), (1, false)]]

def TLow3_336FFTT : Tbl := [([tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, false)]]),
  ([tS 0, tC 1, tS 0], [tg .box [1] [(2, true), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FFTT : check 2 TLow3_336FFTT LLow3_336FFTT RLow3_336FFTT
    [.rw 0 0 true,
    .sem 6 1 [tC 1] 0,
    .sem 0 13 [tp 2 [L.C 0] [1, 2], tZ 1, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]] 0,
    .rw 4 1 true,
    .sem 5 1 [tC 1] 0,
    .sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 3 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) true,
    .swp 6 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 5 2 [] 0,
    .sem 4 1 [tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2] 0,
    .sem 12 1 [tC 0] 2,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]] 0,
    .sem 4 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 5 0 [tS 1, tS 1] 0,
    .swp 6 1 (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [2]) (tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [1]) false,
    .swp 3 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 2 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 4 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FFTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FFTT) (wcT 3 RLow3_336FFTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FFTT

def LLow3_336FTFF : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [1] [(2, false), (0, false)]]

def RLow3_336FTFF : List Tk := [tg .box [1] [(2, false), (0, false)], tg .box [0] [(2, true), (1, false)]]

def TLow3_336FTFF : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FTFF : check 2 TLow3_336FTFF LLow3_336FTFF RLow3_336FTFF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 2] 0,
    .rw 2 1 true,
    .sem 9 1 [tC 1] 0,
    .sem 9 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 8 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 13 [tp 2 [L.C 0] [0, 2], tZ 0, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 1 5 [tp 2 [L.C 0] [0, 2], tZ 0, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0], tZ 2] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 2 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 1 [tC 1] 0,
    .sem 4 1 [tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0] 1,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 0 4 [tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2] 1,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 1 [tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FTFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FTFF) (wcT 3 RLow3_336FTFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FTFF

def LLow3_336FTFT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [1] [(2, true), (0, false)]]

def RLow3_336FTFT : List Tk := [tg .box [1] [(2, true), (0, false)], tg .box [0] [(2, true), (1, false)]]

def TLow3_336FTFT : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tH 0, tZ 0, tH 0, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0], [tg .box [1] [(2, true), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FTFT : check 2 TLow3_336FTFT LLow3_336FTFT RLow3_336FTFT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 2] 0,
    .rw 2 1 true,
    .sem 6 1 [tC 1] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 5 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 7 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 1 2 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 0 2 [tH 0, tZ 0, tH 0, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FTFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FTFT) (wcT 3 RLow3_336FTFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FTFT

def LLow3_336FTTF : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [1] [(2, false), (0, true)]]

def RLow3_336FTTF : List Tk := [tg .box [1] [(2, false), (0, true)], tg .box [0] [(2, true), (1, false)]]

def TLow3_336FTTF : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FTTF : check 2 TLow3_336FTTF LLow3_336FTTF RLow3_336FTTF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 2] 0,
    .rw 2 1 true,
    .sem 6 1 [tC 1] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 5 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 7 [tp 2 [L.C 0] [0, 2], tZ 0] 1,
    .sem 1 3 [tp 2 [L.C 0] [0, 2], tZ 0, tZ 2] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 0 2 [tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FTTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FTTF) (wcT 3 RLow3_336FTTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FTTF

def LLow3_336FTTT : List Tk := [tg .box [0] [(2, true), (1, false)], tg .box [1] [(2, true), (0, true)]]

def RLow3_336FTTT : List Tk := [tg .box [1] [(2, true), (0, true)], tg .box [0] [(2, true), (1, false)]]

def TLow3_336FTTT : Tbl := [([tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1], [tg .box [0] [(2, true), (1, false)]]),
  ([tS 0, tC 1, tS 0], [tg .box [1] [(2, true), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336FTTT : check 2 TLow3_336FTTT LLow3_336FTTT RLow3_336FTTT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 2] 0,
    .rw 2 1 true,
    .sem 3 1 [tC 1] 0,
    .sem 3 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 2 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 1 2 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336FTTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336FTTT) (wcT 3 RLow3_336FTTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336FTTT

def LLow3_336TFFF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [1] [(2, false), (0, false)]]

def RLow3_336TFFF : List Tk := [tg .box [1] [(2, false), (0, false)], tg .box [0] [(2, false), (1, true)]]

def TLow3_336TFFF : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TFFF : check 2 TLow3_336TFFF LLow3_336TFFF RLow3_336TFFF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 1] 0,
    .rw 2 1 true,
    .sem 9 1 [tC 1] 0,
    .sem 9 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 8 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 13 [tp 2 [L.C 0] [0, 2], tZ 0, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sw 2,
    .sw 3,
    .sem 4 2 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0], tZ 1] 2,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 2 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 1 [tC 1] 0,
    .sem 4 1 [tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0] 1,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 0 4 [tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2] 1,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 1 [tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TFFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TFFF) (wcT 3 RLow3_336TFFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TFFF

def LLow3_336TFFT : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [1] [(2, true), (0, false)]]

def RLow3_336TFFT : List Tk := [tg .box [1] [(2, true), (0, false)], tg .box [0] [(2, false), (1, true)]]

def TLow3_336TFFT : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tH 0, tZ 0, tH 0, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0], [tg .box [1] [(2, true), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TFFT : check 2 TLow3_336TFFT LLow3_336TFFT RLow3_336TFFT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 1] 0,
    .rw 2 1 true,
    .sem 6 1 [tC 1] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 5 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 7 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sw 2,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 0 2 [tH 0, tZ 0, tH 0, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TFFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TFFT) (wcT 3 RLow3_336TFFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TFFT

def LLow3_336TFTF : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [1] [(2, false), (0, true)]]

def RLow3_336TFTF : List Tk := [tg .box [1] [(2, false), (0, true)], tg .box [0] [(2, false), (1, true)]]

def TLow3_336TFTF : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TFTF : check 2 TLow3_336TFTF LLow3_336TFTF RLow3_336TFTF
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 1] 0,
    .rw 2 1 true,
    .sem 6 1 [tC 1] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 5 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 2 7 [tp 2 [L.C 0] [0, 2], tZ 0] 1,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sw 2,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 0 2 [tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TFTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TFTF) (wcT 3 RLow3_336TFTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TFTF

def LLow3_336TFTT : List Tk := [tg .box [0] [(2, false), (1, true)], tg .box [1] [(2, true), (0, true)]]

def RLow3_336TFTT : List Tk := [tg .box [1] [(2, true), (0, true)], tg .box [0] [(2, false), (1, true)]]

def TLow3_336TFTT : Tbl := [([tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2], [tg .box [0] [(2, false), (1, true)]]),
  ([tS 0, tC 1, tS 0], [tg .box [1] [(2, true), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TFTT : check 2 TLow3_336TFTT LLow3_336TFTT RLow3_336TFTT
    [.rw 0 0 true,
    .sem 3 1 [tC 1] 0,
    .sem 0 7 [tp 2 [L.C 0] [1, 2], tZ 1] 0,
    .rw 2 1 true,
    .sem 3 1 [tC 1] 0,
    .sem 3 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 2 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 1 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 4 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 3 2 [] 0,
    .sem 2 1 [tZ 2] 0,
    .sem 3 1 [tC 0] 2,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 2 1 [tp 2 [L.C 0] [0, 1]] 2,
    .sem 3 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .swp 1 1 (tp 2 [L.C 0] [0, 1]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 2 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TFTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TFTT) (wcT 3 RLow3_336TFTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TFTT

def LLow3_336TTFF : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [1] [(2, false), (0, false)]]

def RLow3_336TTFF : List Tk := [tg .box [1] [(2, false), (0, false)], tg .box [0] [(2, true), (1, true)]]

def TLow3_336TTFF : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TTFF : check 2 TLow3_336TTFF LLow3_336TTFF RLow3_336TTFF
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .sem 0 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 1 1 true,
    .sem 8 1 [tC 1] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 7 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 1 13 [tp 2 [L.C 0] [0, 2], tZ 0, tZ 2, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 2 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 1 [tC 1] 0,
    .sem 4 1 [tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0, tH 0, tZ 0] 1,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 8 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0] [0]] 1,
    .sem 0 4 [tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0, tH 2, tZ 2, tH 2] 1,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 7 1 [tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TTFF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TTFF) (wcT 3 RLow3_336TTFF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TTFF

def LLow3_336TTFT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [1] [(2, true), (0, false)]]

def RLow3_336TTFT : List Tk := [tg .box [1] [(2, true), (0, false)], tg .box [0] [(2, true), (1, true)]]

def TLow3_336TTFT : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 0, tZ 0, tH 0, tS 0, tC 1, tS 0, tH 0, tZ 0, tH 0], [tg .box [1] [(2, true), (0, false)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TTFT : check 2 TLow3_336TTFT LLow3_336TTFT RLow3_336TTFT
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .sem 0 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 1 1 true,
    .sem 5 1 [tC 1] 0,
    .sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 1 7 [tp 2 [L.C 0] [0, 2], tZ 2] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 2 [tZ 2, tp 2 [L.C 0] [1, 2]] 0,
    .sem 0 2 [tH 0, tZ 0, tH 0, tp 2 [L.C 0] [0, 2], tH 0, tZ 0, tH 0] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TTFT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TTFT) (wcT 3 RLow3_336TTFT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TTFT

def LLow3_336TTTF : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [1] [(2, false), (0, true)]]

def RLow3_336TTTF : List Tk := [tg .box [1] [(2, false), (0, true)], tg .box [0] [(2, true), (1, true)]]

def TLow3_336TTTF : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2], [tg .box [1] [(2, false), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TTTF : check 2 TLow3_336TTTF LLow3_336TTTF RLow3_336TTTF
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .sem 0 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 1 1 true,
    .sem 5 1 [tC 1] 0,
    .sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 1 7 [tp 2 [L.C 0] [0, 2], tZ 0] 1,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tC 1] 0,
    .sem 2 1 [tZ 0] 1,
    .sw 1,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 1 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 1 1 [tZ 0] 1,
    .sem 0 2 [tH 2, tZ 2, tH 2, tp 2 [L.C 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 1 [tC 1] 0,
    .sem 4 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TTTF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TTTF) (wcT 3 RLow3_336TTTF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TTTF

def LLow3_336TTTT : List Tk := [tg .box [0] [(2, true), (1, true)], tg .box [1] [(2, true), (0, true)]]

def RLow3_336TTTT : List Tk := [tg .box [1] [(2, true), (0, true)], tg .box [0] [(2, true), (1, true)]]

def TLow3_336TTTT : Tbl := [([tC 1], [tg .box [0] [(2, true), (1, true)]]),
  ([tS 0, tC 1, tS 0], [tg .box [1] [(2, true), (0, true)]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.C 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [2, 1]])]

theorem runLow3_336TTTT : check 2 TLow3_336TTTT LLow3_336TTTT RLow3_336TTTT
    [.rw 0 0 true,
    .sem 0 1 [tC 1] 0,
    .sem 0 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 1 1 true,
    .sem 2 1 [tC 1] 0,
    .sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 0 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 0 2 false,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tC 1] 0,
    .sem 1 1 [tC 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tLow3_336TTTT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_336TTTT) (wcT 3 RLow3_336TTTT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (W3T.te12 ih)) (AllD.nil 3)))) runLow3_336TTTT

def LLow3_340FF : List Tk := [tg .hg [0, 1] [(2, false)], tg .hg [0, 1] [(2, false)]]

def RLow3_340FF : List Tk := [tg .hg [0, 1] [(2, false)], tg .hg [0, 1] [(2, false)]]

def TLow3_340FF : Tbl := []

theorem runLow3_340FF : check 2 TLow3_340FF LLow3_340FF RLow3_340FF
    [] = true := by
  decide +kernel

theorem tLow3_340FF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_340FF) (wcT 3 RLow3_340FF) :=
  check_sound ih (AllD.nil 3) runLow3_340FF

def LLow3_340FT : List Tk := [tg .hg [0, 1] [(2, false)], tg .hg [0, 1] [(2, true)]]

def RLow3_340FT : List Tk := [tg .hg [0, 1] [(2, true)], tg .hg [0, 1] [(2, false)]]

def TLow3_340FT : Tbl := [([tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2], [tg .hg [0, 1] [(2, false)]]),
  ([tK 1], [tg .hg [0, 1] [(2, true)]])]

theorem runLow3_340FT : check 2 TLow3_340FT LLow3_340FT RLow3_340FT
    [.rw 0 0 true,
    .sem 3 1 [tK 1] 0,
    .rw 7 1 true,
    .sem 7 1 [tK 1] 0,
    .sem 0 8 [tK 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tK 1] 0,
    .rw 1 0 false,
    .sem 0 1 [tK 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_340FT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_340FT) (wcT 3 RLow3_340FT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_340FT

def LLow3_340TF : List Tk := [tg .hg [0, 1] [(2, true)], tg .hg [0, 1] [(2, false)]]

def RLow3_340TF : List Tk := [tg .hg [0, 1] [(2, false)], tg .hg [0, 1] [(2, true)]]

def TLow3_340TF : Tbl := [([tK 1], [tg .hg [0, 1] [(2, true)]]),
  ([tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2], [tg .hg [0, 1] [(2, false)]])]

theorem runLow3_340TF : check 2 TLow3_340TF LLow3_340TF RLow3_340TF
    [.rw 0 0 true,
    .sem 0 1 [tK 1] 0,
    .rw 1 1 true,
    .sem 4 1 [tK 1] 0,
    .sem 0 8 [tH 2, tK 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2] 0,
    .sem 1 7 [tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tK 1] 0,
    .sem 7 1 [tK 1] 0,
    .rw 7 0 false,
    .sem 3 1 [tK 1] 0,
    .rw 0 1 false] = true := by
  decide +kernel

theorem tLow3_340TF (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_340TF) (wcT 3 RLow3_340TF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.nil 3))) runLow3_340TF

def LLow3_340TT : List Tk := [tg .hg [0, 1] [(2, true)], tg .hg [0, 1] [(2, true)]]

def RLow3_340TT : List Tk := [tg .hg [0, 1] [(2, true)], tg .hg [0, 1] [(2, true)]]

def TLow3_340TT : Tbl := []

theorem runLow3_340TT : check 2 TLow3_340TT LLow3_340TT RLow3_340TT
    [] = true := by
  decide +kernel

theorem tLow3_340TT (ih : IH 3) : Derivable (theory 3) (wcT 3 LLow3_340TT) (wcT 3 RLow3_340TT) :=
  check_sound ih (AllD.nil 3) runLow3_340TT

end QCert.RealCliffordCH.Sec8.D.Low3
