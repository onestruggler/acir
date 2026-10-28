/- Three-wire base cases of (335), (336), and (340). -/
import QCert.RealCliffordCH.Sec8.D.W3.Tokens

namespace QCert.RealCliffordCH.Sec8.D.Low3Hg345
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
def Ld133f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]]

def Rd133f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Td133f2 : Tbl := [([tK 1, tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tK 1])]

theorem rund133f2 : check 2 Td133f2 Ld133f2 Rd133f2
    [.sem 1 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.K 0] [0, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tK 1, tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem td133f2 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld133f2) (wcT 3 Rd133f2) :=
  check_sound ih (AllD.cons (W3T.td133 ih) (AllD.nil 3)) rund133f2

def LHg345FF : List Tk := [tg .hg [1, 0] [(2, false)], tg .hg [0, 1] [(2, false)]]

def RHg345FF : List Tk := [tg .hg [0, 1] [(2, false)], tg .hg [1, 0] [(2, false)]]

def THg345FF : Tbl := [([tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2], [tg .hg [1, 0] [(2, false)]]),
  ([tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2], [tg .hg [0, 1] [(2, false)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem runHg345FF : check 2 THg345FF LHg345FF RHg345FF
    [.rw 0 0 true,
    .sem 4 1 [tK 1] 0,
    .sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .rw 1 1 true,
    .sem 4 1 [tK 1] 0,
    .sem 1 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .rw 0 2 true,
    .sem 0 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tH 2, tZ 2, tH 2, tp 2 [L.K 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 5 1 [tK 1] 0,
    .sem 5 1 [tK 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tHg345FF (ih : IH 3) : Derivable (theory 3) (wcT 3 LHg345FF) (wcT 3 RHg345FF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (td133f2 ih) (AllD.nil 3)))) runHg345FF

def LHg345FT : List Tk := [tg .hg [1, 0] [(2, false)], tg .hg [0, 1] [(2, true)]]

def RHg345FT : List Tk := [tg .hg [0, 1] [(2, true)], tg .hg [1, 0] [(2, false)]]

def THg345FT : Tbl := [([tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2], [tg .hg [1, 0] [(2, false)]]),
  ([tK 1], [tg .hg [0, 1] [(2, true)]]),
  ([tK 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 1])]

theorem runHg345FT : check 2 THg345FT LHg345FT RHg345FT
    [.rw 0 0 true,
    .sem 4 1 [tK 1] 0,
    .sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .rw 1 1 true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 1 1 [tK 1] 0,
    .rw 0 2 true,
    .sem 0 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 0 1 [tK 1] 0,
    .sem 0 1 [tK 1] 0,
    .rw 0 1 false,
    .sem 1 1 [tH 2, tZ 2, tH 2, tp 2 [L.K 0] [0, 2], tH 2, tZ 2, tH 2] 1,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 5 1 [tK 1] 0,
    .sem 5 1 [tK 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tHg345FT (ih : IH 3) : Derivable (theory 3) (wcT 3 LHg345FT) (wcT 3 RHg345FT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (W3T.td134 ih) (AllD.nil 3)))) runHg345FT

def LHg345TF : List Tk := [tg .hg [1, 0] [(2, true)], tg .hg [0, 1] [(2, false)]]

def RHg345TF : List Tk := [tg .hg [0, 1] [(2, false)], tg .hg [1, 0] [(2, true)]]

def THg345TF : Tbl := [([tS 0, tK 1, tS 0], [tg .hg [1, 0] [(2, true)]]),
  ([tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2], [tg .hg [0, 1] [(2, false)]]),
  ([tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [0, 2]])]

theorem runHg345TF : check 2 THg345TF LHg345TF RHg345TF
    [.rw 0 0 true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .rw 1 1 true,
    .sem 4 1 [tK 1] 0,
    .sem 1 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .rw 0 2 false,
    .sem 0 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tK 1] 0,
    .rw 0 1 false,
    .swp 1 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 2 1 [tK 1] 0,
    .sem 2 1 [tK 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tHg345TF (ih : IH 3) : Derivable (theory 3) (wcT 3 LHg345TF) (wcT 3 RHg345TF) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (W3T.td134 ih)) (AllD.nil 3)))) runHg345TF

def LHg345TT : List Tk := [tg .hg [1, 0] [(2, true)], tg .hg [0, 1] [(2, true)]]

def RHg345TT : List Tk := [tg .hg [0, 1] [(2, true)], tg .hg [1, 0] [(2, true)]]

def THg345TT : Tbl := [([tS 0, tK 1, tS 0], [tg .hg [1, 0] [(2, true)]]),
  ([tK 1], [tg .hg [0, 1] [(2, true)]]),
  ([tK 1, tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tK 1])]

theorem runHg345TT : check 2 THg345TT LHg345TT RHg345TT
    [.rw 0 0 true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .rw 1 1 true,
    .sem 1 1 [tK 1] 0,
    .sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 1 1 [tK 1] 0,
    .rw 0 2 true,
    .sem 0 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 0 1 [tK 1] 0,
    .sem 0 1 [tK 1] 0,
    .rw 0 1 false,
    .swp 1 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 2 1 [tK 1] 0,
    .sem 2 1 [tK 1] 0,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tHg345TT (ih : IH 3) : Derivable (theory 3) (wcT 3 LHg345TT) (wcT 3 RHg345TT) :=
  check_sound ih (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (W3T.td133 ih) (AllD.nil 3)))) runHg345TT

end QCert.RealCliffordCH.Sec8.D.Low3Hg345
