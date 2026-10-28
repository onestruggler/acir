/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix D.2: the remaining rotation and white-control equations

Certificates reconstructed from the paper's diagram chains. Each table entry
is an earlier proved equation; every run is checked by `decide +kernel`.
-/
import QCert.RealCliffordCH.Sec8.D.W3.Base
import QCert.RealCliffordCH.Sec8.D.W3.Sym

namespace QCert.RealCliffordCH.Sec8.D.W3T
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

def LBridgeLd130 : List Tk := [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tS 1]

def RBridgeLd130 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]]

def TBridgeLd130 : Tbl := []

theorem runBridgeLd130 : check 2 TBridgeLd130 LBridgeLd130 RBridgeLd130
    [.sem 0 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 1 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tBridgeLd130 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd130) (wcT 3 RBridgeLd130) :=
  check_sound ih (AllD.nil 3) runBridgeLd130

def LBridgeRd130 : List Tk := [tS 0, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tS 1, tS 0]

def RBridgeRd130 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]]

def TBridgeRd130 : Tbl := []

theorem runBridgeRd130 : check 2 TBridgeRd130 LBridgeRd130 RBridgeRd130
    [.sem 1 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]) (tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeRd130 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd130) (wcT 3 RBridgeRd130) :=
  check_sound ih (AllD.nil 3) runBridgeRd130

def Ld130 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]]
def Rd130 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]]
theorem td130 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld130) (wcT 3 Rd130) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0, L.K 1, L.H 2, L.Z 1, L.K 1, L.H 2, L.Z 1, L.K 1, L.H 2, L.Z 1, L.S 1]) (Eng.circW 3 [L.S 0, L.K 1, L.H 2, L.Z 1, L.K 1, L.H 2, L.Z 1, L.K 1, L.H 2, L.Z 1, L.S 1, L.S 0]) := d130 ih
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLd130 ih).symm.trans (h.trans (tBridgeRd130 ih))

def LBridgeLd132 : List Tk := [tC 1, tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2]

def RBridgeLd132 : List Tk := [tC 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]]

def TBridgeLd132 : Tbl := []

theorem runBridgeLd132 : check 2 TBridgeLd132 LBridgeLd132 RBridgeLd132
    [.sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem tBridgeLd132 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd132) (wcT 3 RBridgeLd132) :=
  check_sound ih (AllD.nil 3) runBridgeLd132

def LBridgeRd132 : List Tk := [tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2, tC 1]

def RBridgeRd132 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tC 1]

def TBridgeRd132 : Tbl := []

theorem runBridgeRd132 : check 2 TBridgeRd132 LBridgeRd132 RBridgeRd132
    [.sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem tBridgeRd132 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd132) (wcT 3 RBridgeRd132) :=
  check_sound ih (AllD.nil 3) runBridgeRd132

def Ld132 : List Tk := [tC 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]]
def Rd132 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tC 1]
theorem td132 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld132) (wcT 3 Rd132) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.C 1, L.H 2, L.Z 2, L.H 2, L.S 0, L.K 1, L.S 0, L.H 2, L.Z 2, L.H 2]) (Eng.circW 3 [L.H 2, L.Z 2, L.H 2, L.S 0, L.K 1, L.S 0, L.H 2, L.Z 2, L.H 2, L.C 1]) := d132 ih
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLd132 ih).symm.trans (h.trans (tBridgeRd132 ih))

def LBridgeLd133 : List Tk := [tK 1, tS 0, tK 1, tS 0]

def RBridgeLd133 : List Tk := [tK 1, tp 2 [L.K 0] [0, 2]]

def TBridgeLd133 : Tbl := []

theorem runBridgeLd133 : check 2 TBridgeLd133 LBridgeLd133 RBridgeLd133
    [.sem 2 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeLd133 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd133) (wcT 3 RBridgeLd133) :=
  check_sound ih (AllD.nil 3) runBridgeLd133

def LBridgeRd133 : List Tk := [tS 0, tK 1, tS 0, tK 1]

def RBridgeRd133 : List Tk := [tp 2 [L.K 0] [0, 2], tK 1]

def TBridgeRd133 : Tbl := []

theorem runBridgeRd133 : check 2 TBridgeRd133 LBridgeRd133 RBridgeRd133
    [.sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeRd133 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd133) (wcT 3 RBridgeRd133) :=
  check_sound ih (AllD.nil 3) runBridgeRd133

def Ld133 : List Tk := [tK 1, tp 2 [L.K 0] [0, 2]]
def Rd133 : List Tk := [tp 2 [L.K 0] [0, 2], tK 1]
theorem td133 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld133) (wcT 3 Rd133) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.K 1, L.S 0, L.K 1, L.S 0]) (Eng.circW 3 [L.S 0, L.K 1, L.S 0, L.K 1]) := d133 ih
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLd133 ih).symm.trans (h.trans (tBridgeRd133 ih))

def LBridgeLd134 : List Tk := [tK 1, tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2]

def RBridgeLd134 : List Tk := [tK 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]]

def TBridgeLd134 : Tbl := []

theorem runBridgeLd134 : check 2 TBridgeLd134 LBridgeLd134 RBridgeLd134
    [.sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem tBridgeLd134 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd134) (wcT 3 RBridgeLd134) :=
  check_sound ih (AllD.nil 3) runBridgeLd134

def LBridgeRd134 : List Tk := [tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2, tK 1]

def RBridgeRd134 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 1]

def TBridgeRd134 : Tbl := []

theorem runBridgeRd134 : check 2 TBridgeRd134 LBridgeRd134 RBridgeRd134
    [.sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem tBridgeRd134 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd134) (wcT 3 RBridgeRd134) :=
  check_sound ih (AllD.nil 3) runBridgeRd134

def Ld134 : List Tk := [tK 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]]
def Rd134 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 1]
theorem td134 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld134) (wcT 3 Rd134) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.K 1, L.H 2, L.Z 2, L.H 2, L.S 0, L.K 1, L.S 0, L.H 2, L.Z 2, L.H 2]) (Eng.circW 3 [L.H 2, L.Z 2, L.H 2, L.S 0, L.K 1, L.S 0, L.H 2, L.Z 2, L.H 2, L.K 1]) := d134 ih
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLd134 ih).symm.trans (h.trans (tBridgeRd134 ih))

def LBridgeLd135 : List Tk := [tS 0, tK 1, tS 0, tK 0]

def RBridgeLd135 : List Tk := [tp 2 [L.K 0] [0, 2], tK 0]

def TBridgeLd135 : Tbl := []

theorem runBridgeLd135 : check 2 TBridgeLd135 LBridgeLd135 RBridgeLd135
    [.sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeLd135 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd135) (wcT 3 RBridgeLd135) :=
  check_sound ih (AllD.nil 3) runBridgeLd135

def LBridgeRd135 : List Tk := [tK 0, tS 0, tK 1, tS 0]

def RBridgeRd135 : List Tk := [tK 0, tp 2 [L.K 0] [0, 2]]

def TBridgeRd135 : Tbl := []

theorem runBridgeRd135 : check 2 TBridgeRd135 LBridgeRd135 RBridgeRd135
    [.sem 2 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeRd135 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd135) (wcT 3 RBridgeRd135) :=
  check_sound ih (AllD.nil 3) runBridgeRd135

def Ld135 : List Tk := [tp 2 [L.K 0] [0, 2], tK 0]
def Rd135 : List Tk := [tK 0, tp 2 [L.K 0] [0, 2]]
theorem td135 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld135) (wcT 3 Rd135) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.S 0, L.K 1, L.S 0, L.K 0]) (Eng.circW 3 [L.K 0, L.S 0, L.K 1, L.S 0]) := d135 ih
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLd135 ih).symm.trans (h.trans (tBridgeRd135 ih))

def LBridgeLd137 : List Tk := [tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2]

def RBridgeLd137 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]]

def TBridgeLd137 : Tbl := []

theorem runBridgeLd137 : check 2 TBridgeLd137 LBridgeLd137 RBridgeLd137
    [.sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 9 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 8 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 10 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 9 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 4 1 [tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tK 0] 2,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 4 1 [tK 0] 2,
    .sem 5 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 7 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 6 1 [tH 2, tZ 2, tH 2] 0,
    .sem 9 1 [tK 0] 2,
    .sw 8,
    .sw 7,
    .sw 6,
    .sem 7 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 6 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 6 1 [tK 0] 2,
    .sem 7 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 8 2 [] 0] = true := by
  decide +kernel

theorem tBridgeLd137 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd137) (wcT 3 RBridgeLd137) :=
  check_sound ih (AllD.nil 3) runBridgeLd137

def LBridgeRd137 : List Tk := [tK 0, tS 0, tZ 1, tS 0, tK 0, tS 0, tZ 1, tS 0]

def RBridgeRd137 : List Tk := [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [0, 1]]

def TBridgeRd137 : Tbl := []

theorem runBridgeRd137 : check 2 TBridgeRd137 LBridgeRd137 RBridgeRd137
    [.sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 3 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 3 0 [tS 0, tS 0] 2,
    .sem 2 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 1 0 (tp 1 [L.Z 0] [1]) (tp 1 [L.Z 0] [0]) false,
    .sem 4 0 [tS 0, tS 0] 2,
    .swp 2 0 (tp 2 [L.K 0] [1, 0]) (tp 2 [L.K 0] [0, 1]) false,
    .sem 4 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 3 0 (tp 1 [L.Z 0] [1]) (tp 1 [L.Z 0] [0]) false,
    .sem 0 4 [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [0, 1]] 2] = true := by
  decide +kernel

theorem tBridgeRd137 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd137) (wcT 3 RBridgeRd137) :=
  check_sound ih (AllD.nil 3) runBridgeRd137

def Ld137 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]]
def Rd137 : List Tk := [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [0, 1]]
theorem td137 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld137) (wcT 3 Rd137) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.H 2, L.Z 2, L.H 2, L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0, L.H 2, L.Z 2, L.H 2]) (Eng.circW 3 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0]) := d137 ih
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLd137 ih).symm.trans (h.trans (tBridgeRd137 ih))

def LBridgeLe12 : List Tk := [tC 1, tC 0]

def RBridgeLe12 : List Tk := [tC 1, tC 0]

def TBridgeLe12 : Tbl := []

theorem runBridgeLe12 : check 2 TBridgeLe12 LBridgeLe12 RBridgeLe12
    [] = true := by
  decide +kernel

theorem tBridgeLe12 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLe12) (wcT 3 RBridgeLe12) :=
  check_sound ih (AllD.nil 3) runBridgeLe12

def LBridgeRe12 : List Tk := [tC 0, tC 1]

def RBridgeRe12 : List Tk := [tC 0, tC 1]

def TBridgeRe12 : Tbl := []

theorem runBridgeRe12 : check 2 TBridgeRe12 LBridgeRe12 RBridgeRe12
    [] = true := by
  decide +kernel

theorem tBridgeRe12 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRe12) (wcT 3 RBridgeRe12) :=
  check_sound ih (AllD.nil 3) runBridgeRe12

def Le12 : List Tk := [tC 1, tC 0]
def Re12 : List Tk := [tC 0, tC 1]
theorem te12 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le12) (wcT 3 Re12) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.C 1, L.C 0]) (Eng.circW 3 [L.C 0, L.C 1]) := t_e12
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLe12 ih).symm.trans (h.trans (tBridgeRe12 ih))

def LBridgeLe13 : List Tk := [tC 1, tK 0]

def RBridgeLe13 : List Tk := [tC 1, tK 0]

def TBridgeLe13 : Tbl := []

theorem runBridgeLe13 : check 2 TBridgeLe13 LBridgeLe13 RBridgeLe13
    [] = true := by
  decide +kernel

theorem tBridgeLe13 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLe13) (wcT 3 RBridgeLe13) :=
  check_sound ih (AllD.nil 3) runBridgeLe13

def LBridgeRe13 : List Tk := [tK 0, tC 1]

def RBridgeRe13 : List Tk := [tK 0, tC 1]

def TBridgeRe13 : Tbl := []

theorem runBridgeRe13 : check 2 TBridgeRe13 LBridgeRe13 RBridgeRe13
    [] = true := by
  decide +kernel

theorem tBridgeRe13 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRe13) (wcT 3 RBridgeRe13) :=
  check_sound ih (AllD.nil 3) runBridgeRe13

def Le13 : List Tk := [tC 1, tK 0]
def Re13 : List Tk := [tK 0, tC 1]
theorem te13 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le13) (wcT 3 Re13) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.C 1, L.K 0]) (Eng.circW 3 [L.K 0, L.C 1]) := t_e13
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLe13 ih).symm.trans (h.trans (tBridgeRe13 ih))

def LBridgeLe14 : List Tk := [tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0]

def RBridgeLe14 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]]

def TBridgeLe14 : Tbl := []

theorem runBridgeLe14 : check 2 TBridgeLe14 LBridgeLe14 RBridgeLe14
    [.sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeLe14 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLe14) (wcT 3 RBridgeLe14) :=
  check_sound ih (AllD.nil 3) runBridgeLe14

def LBridgeRe14 : List Tk := [tS 0, tK 1, tS 0, tC 0, tS 0, tK 1, tS 0, tC 0]

def RBridgeRe14 : List Tk := [tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2], tC 0]

def TBridgeRe14 : Tbl := []

theorem runBridgeRe14 : check 2 TBridgeRe14 LBridgeRe14 RBridgeRe14
    [.sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 3 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 2 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false] = true := by
  decide +kernel

theorem tBridgeRe14 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRe14) (wcT 3 RBridgeRe14) :=
  check_sound ih (AllD.nil 3) runBridgeRe14

def Le14 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]]
def Re14 : List Tk := [tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2], tC 0]
theorem te14 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le14) (wcT 3 Re14) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.K 0, L.S 0, L.C 1, L.S 0, L.K 0, L.S 0, L.C 1, L.S 0]) (Eng.circW 3 [L.S 0, L.K 1, L.S 0, L.C 0, L.S 0, L.K 1, L.S 0, L.C 0]) := t_e14
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLe14 ih).symm.trans (h.trans (tBridgeRe14 ih))

def LBridgeLe17 : List Tk := [tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2, tK 0, tK 1, tK 0]

def RBridgeLe17 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tK 1, tK 0]

def TBridgeLe17 : Tbl := []

theorem runBridgeLe17 : check 2 TBridgeLe17 LBridgeLe17 RBridgeLe17
    [.sem 4 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem tBridgeLe17 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLe17) (wcT 3 RBridgeLe17) :=
  check_sound ih (AllD.nil 3) runBridgeLe17

def LBridgeRe17 : List Tk := [tK 0, tK 1, tK 0, tH 2, tZ 2, tH 2, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2]

def RBridgeRe17 : List Tk := [tK 0, tK 1, tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]]

def TBridgeRe17 : Tbl := []

theorem runBridgeRe17 : check 2 TBridgeRe17 LBridgeRe17 RBridgeRe17
    [.sem 7 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem tBridgeRe17 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRe17) (wcT 3 RBridgeRe17) :=
  check_sound ih (AllD.nil 3) runBridgeRe17

def Le17 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tK 1, tK 0]
def Re17 : List Tk := [tK 0, tK 1, tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]]
theorem te17 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le17) (wcT 3 Re17) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.H 2, L.Z 2, L.H 2, L.S 0, L.C 1, L.S 0, L.H 2, L.Z 2, L.H 2, L.K 0, L.K 1, L.K 0]) (Eng.circW 3 [L.K 0, L.K 1, L.K 0, L.H 2, L.Z 2, L.H 2, L.S 0, L.C 1, L.S 0, L.H 2, L.Z 2, L.H 2]) := t_e17
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLe17 ih).symm.trans (h.trans (tBridgeRe17 ih))

def LBridgeLe18 : List Tk := [tC 1, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0]

def RBridgeLe18 : List Tk := [tC 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def TBridgeLe18 : Tbl := []

theorem runBridgeLe18 : check 2 TBridgeLe18 LBridgeLe18 RBridgeLe18
    [.sem 1 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2] = true := by
  decide +kernel

theorem tBridgeLe18 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLe18) (wcT 3 RBridgeLe18) :=
  check_sound ih (AllD.nil 3) runBridgeLe18

def LBridgeRe18 : List Tk := [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0, tK 1]

def RBridgeRe18 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 1]

def TBridgeRe18 : Tbl := []

theorem runBridgeRe18 : check 2 TBridgeRe18 LBridgeRe18 RBridgeRe18
    [.sem 0 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2] = true := by
  decide +kernel

theorem tBridgeRe18 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRe18) (wcT 3 RBridgeRe18) :=
  check_sound ih (AllD.nil 3) runBridgeRe18

def Le18 : List Tk := [tC 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]
def Re18 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 1]
theorem te18 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le18) (wcT 3 Re18) := by
  have h : Derivable (theory 3) (Eng.circW 3 [L.C 1, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0]) (Eng.circW 3 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0, L.K 1]) := t_e18
  rw [circW_eq_wcT, circW_eq_wcT] at h
  exact (tBridgeLe18 ih).symm.trans (h.trans (tBridgeRe18 ih))

def Le14f1 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.C 0] [0, 2]]

def Re14f1 : List Tk := [tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def Te14f1 : Tbl := [([tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2], tC 0])]

theorem rune14f1 : check 2 Te14f1 Le14f1 Re14f1
    [.sem 4 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .swp 6 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .sem 5 2 [] 2,
    .sem 4 1 [tC 1] 0,
    .sem 5 1 [tH 0, tZ 0, tH 0] 1,
    .sw 4,
    .sw 5,
    .sw 6,
    .sem 7 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 5 0 [tS 0, tS 0] 2,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 3 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .sem 2 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tK 0, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .swp 1 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .swp 4 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .sem 3 2 [] 2,
    .sem 2 1 [tC 1] 0,
    .sem 3 1 [tH 0, tZ 0, tH 0] 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 3 0 [tS 0, tS 0] 2,
    .swp 4 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .swp 1 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tK 0, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 2 2 [] 0,
    .sem 3 2 [] 0,
    .sem 4 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 5 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 8 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .swp 0 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 2 2 [] 2,
    .sem 1 1 [tH 0, tZ 0, tH 0] 1,
    .sem 4 1 [tK 1] 0,
    .sw 3,
    .sw 2,
    .sw 1,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 1 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 2 0 [tS 0, tS 0] 2,
    .swp 3 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .swp 0 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 1 2 [] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .swp 2 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .swp 5 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 4 2 [] 2,
    .sem 3 1 [tH 0, tZ 0, tH 0] 1,
    .sem 6 1 [tK 1] 0,
    .sw 5,
    .sw 4,
    .sw 3,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 3 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 4 0 [tS 0, tS 0] 2,
    .swp 5 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .swp 2 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 3 2 [] 0,
    .sem 3 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2] = true := by
  decide +kernel

theorem te14f1 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le14f1) (wcT 3 Re14f1) :=
  check_sound ih (AllD.cons (te14 ih) (AllD.nil 3)) rune14f1

def Le14i : List Tk := [tC 0, tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2]]

def Re14i : List Tk := [tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0]

def Te14i : Tbl := [([tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2], tC 0])]

theorem rune14i : check 2 Te14i Le14i Re14i
    [.sem 4 0 [tK 0, tK 0] 2,
    .sem 5 0 [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [0, 2]] 1,
    .sem 6 0 [tK 0, tK 0] 2,
    .sem 7 0 [tp 2 [L.C 0] [0, 2], tp 2 [L.C 0] [0, 2]] 1,
    .rw 4 0 false,
    .sem 3 2 [] 1,
    .sem 2 2 [] 2,
    .sem 1 2 [] 1,
    .sem 0 2 [] 2] = true := by
  decide +kernel

theorem te14i (ih : IH 3) : Derivable (theory 3) (wcT 3 Le14i) (wcT 3 Re14i) :=
  check_sound ih (AllD.cons (te14 ih) (AllD.nil 3)) rune14i

def Le14if1 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.K 0] [0, 2]]

def Re14if1 : List Tk := [tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def Te14if1 : Tbl := [([tC 0, tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2]], [tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0])]

theorem rune14if1 : check 2 Te14if1 Le14if1 Re14if1
    [.sem 4 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .swp 3 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .swp 6 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .sem 5 2 [] 2,
    .sem 4 1 [tK 1] 0,
    .sem 5 1 [tH 0, tZ 0, tH 0] 1,
    .sw 4,
    .sw 5,
    .sw 6,
    .sem 7 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 5 0 [tS 0, tS 0] 2,
    .swp 6 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 3 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .sem 2 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tC 0, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .swp 1 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .swp 4 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .sem 3 2 [] 2,
    .sem 2 1 [tK 1] 0,
    .sem 3 1 [tH 0, tZ 0, tH 0] 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 3 0 [tS 0, tS 0] 2,
    .swp 4 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 1 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tC 0, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 2 2 [] 0,
    .sem 3 2 [] 0,
    .sem 4 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 5 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 8 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .swp 0 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 2 2 [] 2,
    .sem 1 1 [tH 0, tZ 0, tH 0] 1,
    .sem 4 1 [tC 1] 0,
    .sw 3,
    .sw 2,
    .sw 1,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 2 0 [tS 0, tS 0] 2,
    .swp 3 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .swp 0 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 1 2 [] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .swp 2 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) true,
    .swp 5 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) true,
    .sem 4 2 [] 2,
    .sem 3 1 [tH 0, tZ 0, tH 0] 1,
    .sem 6 1 [tC 1] 0,
    .sw 5,
    .sw 4,
    .sw 3,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 3 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 4 0 [tS 0, tS 0] 2,
    .swp 5 0 (tp 1 [L.H 0, L.Z 0, L.H 0] [0]) (tp 1 [L.H 0, L.Z 0, L.H 0] [1]) false,
    .swp 2 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 3 2 [] 0,
    .sem 3 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2] = true := by
  decide +kernel

theorem te14if1 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le14if1) (wcT 3 Re14if1) :=
  check_sound ih (AllD.cons (te14i ih) (AllD.nil 3)) rune14if1

def Ld132f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]]

def Rd132f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Td132f2 : Tbl := [([tC 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tC 1])]

theorem rund132f2 : check 2 Td132f2 Ld132f2 Rd132f2
    [.sem 1 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tC 1, tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem td132f2 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld132f2) (wcT 3 Rd132f2) :=
  check_sound ih (AllD.cons (td132 ih) (AllD.nil 3)) rund132f2

def Le18i : List Tk := [tK 1, tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]]

def Re18i : List Tk := [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tC 1]

def Te18i : Tbl := [([tC 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 1])]

theorem rune18i : check 2 Te18i Le18i Re18i
    [.sem 2 0 [tC 1, tC 1] 0,
    .sem 3 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 2 0 false,
    .sem 1 2 [] 2,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem te18i (ih : IH 3) : Derivable (theory 3) (wcT 3 Le18i) (wcT 3 Re18i) :=
  check_sound ih (AllD.cons (te18 ih) (AllD.nil 3)) rune18i

def Le18f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def Re18f2 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Te18f2 : Tbl := [([tC 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 1])]

theorem rune18f2 : check 2 Te18f2 Le18f2 Re18f2
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sem 11 1 [tH 2, tZ 2, tH 2] 0,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 1,
    .sw 2,
    .sw 3,
    .sem 4 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tC 1, tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 1 [tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 2,
    .sw 1,
    .sw 0,
    .sw 3,
    .sw 2,
    .sw 1,
    .sw 4,
    .sw 3,
    .sw 2,
    .sw 5,
    .sw 4,
    .sw 3,
    .sw 6,
    .sw 5,
    .sw 4,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 11,
    .sw 10,
    .sw 9,
    .sem 10 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 1 2 [] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem te18f2 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le18f2) (wcT 3 Re18f2) :=
  check_sound ih (AllD.cons (te18 ih) (AllD.nil 3)) rune18f2

def Le17f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0]

def Re17f2 : List Tk := [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]]

def Te17f2 : Tbl := [([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tK 1, tK 0], [tK 0, tK 1, tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2]])]

theorem rune17f2 : check 2 Te17f2 Le17f2 Re17f2
    [.sem 4 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 3 1 [tK 0] 2,
    .sem 4 1 [tH 2, tZ 2, tH 2] 0,
    .sw 3,
    .sw 4,
    .sw 5,
    .sem 6 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 1 [tK 0] 2,
    .sem 2 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tK 1, tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 1 1 [tK 0] 2,
    .sem 2 1 [tH 2, tZ 2, tH 2] 0,
    .sw 1,
    .sw 2,
    .sw 3,
    .sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 1 [tK 0] 2,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [0, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 2 2 [] 0,
    .sem 3 2 [] 0,
    .sem 4 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 0 1 [tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tK 0] 2,
    .sw 2,
    .sw 1,
    .sw 0,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 0 1 [tK 0] 2,
    .sem 1 2 [] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 3 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 2 1 [tH 2, tZ 2, tH 2] 0,
    .sem 5 1 [tK 0] 2,
    .sw 4,
    .sw 3,
    .sw 2,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 2 1 [tK 0] 2,
    .sem 3 2 [] 0,
    .sem 3 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]] 1] = true := by
  decide +kernel

theorem te17f2 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le17f2) (wcT 3 Re17f2) :=
  check_sound ih (AllD.cons (te17 ih) (AllD.nil 3)) rune17f2

def L139Inner : List Tk := [tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0]]

def R139Inner : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [0, 2]]

def T139Inner : Tbl := [([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.K 0] [0, 2], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0], tp 2 [L.C 0] [0, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0], [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]])]

theorem run139Inner : check 2 T139Inner L139Inner R139Inner
    [.sem 0 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .rw 0 0 true,
    .sem 1 1 [tp 2 [L.K 0] [0, 2]] 1,
    .sem 5 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 0] 2,
    .rw 3 1 false,
    .sem 2 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 0] 2,
    .sem 2 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0]] 2,
    .rw 1 2 false,
    .sem 1 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 2 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .rw 2 3 false,
    .sem 5 1 [tp 2 [L.C 0] [0, 2]] 1,
    .sem 1 2 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 2 1 true,
    .sem 3 2 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0]] 2,
    .rw 4 2 true,
    .sem 5 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 5 2 [] 2] = true := by
  decide +kernel

theorem t139Inner (ih : IH 3) : Derivable (theory 3) (wcT 3 L139Inner) (wcT 3 R139Inner) :=
  check_sound ih (AllD.cons (td132f2 ih) (AllD.cons (te18f2 ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te18i ih)) (AllD.cons (te17f2 ih) (AllD.nil 3))))) run139Inner

def L139InnerInv : List Tk := [tp 2 [L.K 0] [0, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def R139InnerInv : List Tk := [tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [0, 2]]

def T139InnerInv : Tbl := [([tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [0, 2]])]

theorem run139InnerInv : check 2 T139InnerInv L139InnerInv R139InnerInv
    [.sem 5 0 [tp 2 [L.K 0] [0, 2], tp 2 [L.K 0] [0, 2]] 1,
    .sem 6 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 7 0 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 0]] 2,
    .sem 8 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 9 0 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 0]] 2,
    .rw 5 0 false,
    .sem 4 2 [] 0,
    .sem 3 2 [] 2,
    .sem 2 2 [] 0,
    .sem 1 2 [] 2,
    .sem 0 2 [] 1] = true := by
  decide +kernel

theorem t139InnerInv (ih : IH 3) : Derivable (theory 3) (wcT 3 L139InnerInv) (wcT 3 R139InnerInv) :=
  check_sound ih (AllD.cons (t139Inner ih) (AllD.nil 3)) run139InnerInv

def Le13f2 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0]

def Re13f2 : List Tk := [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Te13f2 : Tbl := [([tC 1, tK 0], [tK 0, tC 1])]

theorem rune13f2 : check 2 Te13f2 Le13f2 Re13f2
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 1 1 [tK 0] 2,
    .sem 2 1 [tH 2, tZ 2, tH 2] 0,
    .sw 1,
    .sw 2,
    .sw 3,
    .sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 1 [tK 0] 2,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tC 1, tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 0 1 [tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tK 0] 2,
    .sw 2,
    .sw 1,
    .sw 0,
    .sem 1 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 0 1 [tK 0] 2,
    .sem 1 2 [] 0,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem te13f2 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le13f2) (wcT 3 Re13f2) :=
  check_sound ih (AllD.cons (te13 ih) (AllD.nil 3)) rune13f2

def Ld139 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Rd139 : List Tk := [tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]]

def Td139 : Tbl := [([tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tC 0, tp 2 [L.K 0] [0, 2], tC 0]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.C 0] [1, 0]], [tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0]], [tp 2 [L.C 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.K 0] [0, 2], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0], tp 2 [L.C 0] [0, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0], [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]]),
  ([tp 2 [L.K 0] [0, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]], [tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [0, 2]])]

theorem rund139 : check 2 Td139 Ld139 Rd139
    [.rw 0 0 false,
    .rw 4 1 true,
    .sem 7 1 [tC 0] 2,
    .sem 5 1 [tC 0] 2,
    .sem 3 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 5 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 3 2 true,
    .sem 2 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .rw 2 3 true,
    .sem 3 1 [tp 2 [L.K 0] [0, 2]] 1,
    .sem 7 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 0] 2,
    .rw 5 4 false,
    .sem 4 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 0] 2,
    .sem 4 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0]] 2,
    .rw 3 5 false,
    .sem 3 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 2]] 1,
    .rw 4 6 false,
    .sem 7 1 [tp 2 [L.C 0] [0, 2]] 1,
    .sem 3 2 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 4 4 true,
    .sem 5 2 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 0]] 2,
    .rw 6 5 true,
    .sem 7 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 7 2 [] 2,
    .rw 2 2 false,
    .sem 2 1 [tC 0] 2,
    .sem 4 1 [tC 0] 2,
    .sem 1 2 [] 2,
    .sem 4 0 [tC 0, tC 0] 2,
    .sem 2 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 4 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 1 1 false,
    .rw 0 7 false,
    .rw 4 0 true] = true := by
  decide +kernel

theorem td139 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld139) (wcT 3 Rd139) :=
  check_sound ih (AllD.cons (te14 ih) (AllD.cons (rel_entry havailNone [1, 0] (by decide +kernel) (te14f1 ih)) (AllD.cons (rel_entry havailNone [1, 0] (by decide +kernel) (te14if1 ih)) (AllD.cons (td132f2 ih) (AllD.cons (te18f2 ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te18i ih)) (AllD.cons (te17f2 ih) (AllD.cons (t139InnerInv ih) (AllD.nil 3))))))))) rund139

def Ld140 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0]]

def Rd140 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]]

def Td140 : Tbl := [([tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]], [tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]])]

theorem rund140 : check 2 Td140 Ld140 Rd140
    [.sem 0 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 1 0 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 0]] 2,
    .sem 2 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 3 0 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 0]] 2,
    .rw 4 0 true,
    .sem 11 2 [] 0,
    .sem 10 2 [] 2,
    .sem 9 2 [] 0,
    .sem 8 2 [] 2] = true := by
  decide +kernel

theorem td140 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld140) (wcT 3 Rd140) :=
  check_sound ih (AllD.cons (td139 ih) (AllD.nil 3)) rund140

def Ld145 : List Tk := [tp 2 [L.K 0] [1, 0], tC 0, tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2]]

def Rd145 : List Tk := [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2], tp 2 [L.K 0] [1, 0], tC 0]

def Td145 : Tbl := [([tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 0]], [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0], tp 2 [L.C 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0], tp 2 [L.C 0] [1, 2]], [tp 2 [L.K 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 0]]),
  ([tC 1, tC 0], [tC 0, tC 1]),
  ([tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2]], [tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0]]),
  ([tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2]], [tp 2 [L.C 0] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2], tp 2 [L.K 0] [1, 0]]),
  ([tp 2 [L.K 0] [1, 2], tp 2 [L.K 0] [1, 0]], [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 2]])]

theorem rund145 : check 2 Td145 Ld145 Rd145
    [.rw 2 0 true,
    .sem 5 1 [tC 0] 2,
    .rw 6 1 true,
    .sem 9 1 [tC 1] 0,
    .sem 7 1 [tC 1] 0,
    .sem 5 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0], tC 0] 2,
    .rw 6 2 true,
    .rw 6 2 false,
    .sem 6 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 5 2 [tp 2 [L.C 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0]] 2,
    .rw 2 3 true,
    .sem 5 1 [tC 1] 0,
    .sem 3 1 [tC 1] 0,
    .sem 3 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 2 3 false,
    .sem 2 1 [tK 1] 0,
    .sem 3 1 [tC 0] 2,
    .sem 4 1 [tK 1] 0,
    .sem 5 1 [tC 0] 2,
    .sem 1 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 2 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 3 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .rw 1 4 false,
    .sem 1 1 [tC 1] 0,
    .sem 3 1 [tC 1] 0,
    .sem 5 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0], tC 0] 2,
    .rw 6 2 true,
    .sem 7 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0], tC 0] 2,
    .rw 8 2 true,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 5 1 false,
    .sem 5 1 [tK 1] 0,
    .sem 6 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 1]] 2,
    .sem 7 1 [tK 1] 0,
    .sem 8 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 1]] 2,
    .sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .rw 4 5 true,
    .sem 4 1 [tK 1] 0,
    .sem 5 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 1], tp 2 [L.K 0] [1, 0]] 2,
    .sem 7 1 [tp 2 [L.K 0] [1, 2]] 0,
    .rw 6 5 true,
    .sem 6 1 [tK 1] 0,
    .sem 7 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 1], tp 2 [L.K 0] [1, 0]] 2,
    .sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 5 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 0]] 2,
    .sem 6 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 7 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 0]] 2,
    .rw 4 1 true,
    .sem 7 1 [tC 1] 0,
    .sem 5 1 [tC 1] 0,
    .sem 1 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 3 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 0 3 false,
    .sem 3 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0], tp 2 [L.C 0] [1, 0]] 2,
    .sem 4 1 [tC 0] 2,
    .rw 4 2 true,
    .rw 4 2 false,
    .sem 3 2 [tC 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 0]] 2,
    .sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 7 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 4 1 false,
    .sem 3 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 0 0 false] = true := by
  decide +kernel

theorem td145 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld145) (wcT 3 Rd145) :=
  check_sound ih (AllD.cons (rel_entry havailNone [1, 0] (by decide +kernel) (td137 ih)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te14f1 ih)) (AllD.cons (te12 ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te14 ih)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te14i ih)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (td135 ih)) (AllD.nil 3))))))) rund145

def Le13f2f1 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def Re13f2f1 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]]

def Te13f2f1 : Tbl := [([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0], [tK 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem rune13f2f1 : check 2 Te13f2f1 Le13f2f1 Re13f2f1
    [.sem 1 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tK 0, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 1 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0] = true := by
  decide +kernel

theorem te13f2f1 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le13f2f1) (wcT 3 Re13f2f1) :=
  check_sound ih (AllD.cons (te13f2 ih) (AllD.nil 3)) rune13f2f1

def L146Prefix : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def R146Prefix : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tC 1, tC 0, tK 1, tC 0, tC 1, tZ 2, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [2]]

def T146Prefix : Tbl := [([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 1]]),
  ([tC 1, tK 0], [tK 0, tC 1]),
  ([tK 1, tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tC 1]),
  ([tC 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 1]),
  ([tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2]], [tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0]])]

theorem run146Prefix : check 2 T146Prefix L146Prefix R146Prefix
    [.sem 4 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tK 1] 0,
    .sem 2 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sem 9 1 [tH 2, tZ 2, tH 2] 0,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 2,
    .sw 3,
    .sw 4,
    .sem 5 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tK 1] 0,
    .sem 5 1 [tH 2, tZ 2, tH 2] 0,
    .sem 8 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
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
    .sem 12 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 3 1 [tK 0, tH 0] 2,
    .sem 6 1 [tH 0, tK 0] 2,
    .sw 4,
    .sem 5 2 [] 1,
    .sem 2 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 1]] 0,
    .sem 3 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .rw 2 0 false,
    .sem 2 1 [tK 0] 2,
    .sem 3 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 3 1 [tC 1, tZ 2] 0,
    .rw 2 1 true,
    .sw 3,
    .sem 2 2 [tZ 2, tC 1] 0,
    .sem 1 2 [tZ 2, tK 1] 0,
    .sem 7 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0] [1, 0]] 2,
    .sem 6 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 5 2 false,
    .sem 5 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0] [1, 0]] 2,
    .rw 3 3 false,
    .sem 3 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 2 2 false,
    .sem 2 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 8 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sem 18 1 [tH 2, tZ 2, tH 2] 0,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 0 [tC 1, tC 1] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 5 4 false,
    .sem 5 1 [tK 1] 0,
    .sem 6 1 [tC 0] 2,
    .sem 7 1 [tK 1] 0,
    .sem 8 1 [tC 0] 2,
    .sem 4 2 [] 0,
    .sem 1 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 1 1 [tZ 2] 0,
    .sem 2 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 1 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 2 1 [tZ 2] 0,
    .sem 2 2 [tC 1, tZ 2] 0,
    .sw 3,
    .sem 4 2 [tK 1, tZ 2] 0,
    .sw 5,
    .sem 6 2 [tC 1, tZ 2] 0,
    .sem 8 1 [tH 2, tZ 2, tH 2] 0,
    .sem 11 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sem 18 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2] = true := by
  decide +kernel

theorem t146Prefix (ih : IH 3) : Derivable (theory 3) (wcT 3 L146Prefix) (wcT 3 R146Prefix) :=
  check_sound ih (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (td132f2 ih)) (AllD.cons (te13 ih) (AllD.cons (te18i ih) (AllD.cons (te18 ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te14 ih)) (AllD.nil 3)))))) run146Prefix

def L146PrefixInv : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tZ 2, tC 1, tC 0, tK 1, tC 0, tC 1, tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [2]]

def R146PrefixInv : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def T146PrefixInv : Tbl := [([tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tC 1, tC 0, tK 1, tC 0, tC 1, tZ 2, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [2]])]

theorem run146PrefixInv : check 2 T146PrefixInv L146PrefixInv R146PrefixInv
    [.sem 10 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 11 0 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 12 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 13 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 14 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .rw 10 0 false,
    .sem 9 2 [] 0,
    .sem 8 2 [] 2,
    .sem 7 2 [] 0,
    .sem 6 2 [] 2,
    .sem 5 2 [] 0,
    .sem 4 2 [] 2,
    .sem 3 2 [] 0,
    .sem 2 2 [] 0,
    .sem 1 2 [] 2,
    .sem 0 2 [] 0] = true := by
  decide +kernel

theorem t146PrefixInv (ih : IH 3) : Derivable (theory 3) (wcT 3 L146PrefixInv) (wcT 3 R146PrefixInv) :=
  check_sound ih (AllD.cons (t146Prefix ih) (AllD.nil 3)) run146PrefixInv

def Ld146 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def Rd146 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Td146 : Tbl := [([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 1]]),
  ([tC 1, tK 0], [tK 0, tC 1]),
  ([tK 1, tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tC 1]),
  ([tC 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tK 1]),
  ([tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2]], [tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tZ 2, tC 1, tC 0, tK 1, tC 0, tC 1, tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]])]

theorem rund146 : check 2 Td146 Ld146 Rd146
    [.sem 4 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tK 1] 0,
    .sem 2 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sem 9 1 [tH 2, tZ 2, tH 2] 0,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 2,
    .sw 3,
    .sw 4,
    .sem 5 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tK 1] 0,
    .sem 5 1 [tH 2, tZ 2, tH 2] 0,
    .sem 8 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
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
    .sem 12 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 3 1 [tK 0, tH 0] 2,
    .sem 6 1 [tH 0, tK 0] 2,
    .sw 4,
    .sem 5 2 [] 1,
    .sem 2 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 1]] 0,
    .sem 3 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .rw 2 0 false,
    .sem 2 1 [tK 0] 2,
    .sem 3 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 3 1 [tC 1, tZ 2] 0,
    .rw 2 1 true,
    .sw 3,
    .sem 2 2 [tZ 2, tC 1] 0,
    .sem 1 2 [tZ 2, tK 1] 0,
    .sem 7 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0] [1, 0]] 2,
    .sem 6 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 5 2 false,
    .sem 5 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0] [1, 0]] 2,
    .rw 3 3 false,
    .sem 3 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 2 2 false,
    .sem 2 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 8 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sem 18 1 [tH 2, tZ 2, tH 2] 0,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 0 [tC 1, tC 1] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 5 4 false,
    .sem 5 1 [tK 1] 0,
    .sem 6 1 [tC 0] 2,
    .sem 7 1 [tK 1] 0,
    .sem 8 1 [tC 0] 2,
    .sem 4 2 [] 0,
    .sem 1 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 1 1 [tZ 2] 0,
    .sem 2 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 1 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 2 1 [tZ 2] 0,
    .sem 2 2 [tC 1, tZ 2] 0,
    .sw 3,
    .sem 4 2 [tK 1, tZ 2] 0,
    .sw 5,
    .sem 6 2 [tC 1, tZ 2] 0,
    .sem 8 1 [tH 2, tZ 2, tH 2] 0,
    .sem 11 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sem 18 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 1 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 6 2 [tZ 2, tC 1] 0,
    .sw 5,
    .sem 4 2 [tZ 2, tK 1] 0,
    .sw 3,
    .sem 2 2 [tZ 2, tC 1] 0,
    .sem 8 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 0 1 [tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tS 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0] 2,
    .sw 2,
    .sw 1,
    .sw 0,
    .sw 3,
    .sw 2,
    .sw 1,
    .sw 4,
    .sw 3,
    .sw 2,
    .sw 5,
    .sw 4,
    .sw 3,
    .sw 6,
    .sw 5,
    .sw 4,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 11,
    .sw 10,
    .sw 9,
    .sem 10 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 10 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 8 1 [tS 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0] 2,
    .sem 18 1 [tH 2, tZ 2, tH 2] 0,
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
    .sem 11 10 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 1 [tH 2, tZ 2, tH 2] 0,
    .sem 11 1 [tS 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0] 2,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 18,
    .sw 17,
    .sw 16,
    .sw 19,
    .sw 18,
    .sw 17,
    .sem 18 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 10 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 8 1 [tS 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0] 2,
    .sem 18 1 [tH 2, tZ 2, tH 2] 0,
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
    .sem 11 10 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 1 [tH 2, tZ 2, tH 2] 0,
    .sem 11 1 [tS 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0] 2,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 18,
    .sw 17,
    .sw 16,
    .sw 19,
    .sw 18,
    .sw 17,
    .sem 18 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 10 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 0 1 [tS 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0, tZ 0, tH 1, tK 0] 2,
    .sem 10 1 [tH 2, tZ 2, tH 2] 0,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 0,
    .sw 1,
    .sw 2,
    .sem 3 10 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 5 false,
    .sem 3 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem td146 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld146) (wcT 3 Rd146) :=
  check_sound ih (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (td132f2 ih)) (AllD.cons (te13 ih) (AllD.cons (te18i ih) (AllD.cons (te18 ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te14 ih)) (AllD.cons (t146PrefixInv ih) (AllD.nil 3))))))) rund146

def Le13f1 : List Tk := [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def Re13f1 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]]

def Te13f1 : Tbl := [([tC 1, tK 0], [tK 0, tC 1])]

theorem rune13f1 : check 2 Te13f1 Le13f1 Re13f1
    [.sem 1 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tK 0, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 2,
    .sem 0 1 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tC 1, tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 2 [] 0,
    .rw 1 0 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 1 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0] = true := by
  decide +kernel

theorem te13f1 (ih : IH 3) : Derivable (theory 3) (wcT 3 Le13f1) (wcT 3 Re13f1) :=
  check_sound ih (AllD.cons (te13 ih) (AllD.nil 3)) rune13f1

def Ld147 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [0, 2], tK 0, tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def Rd147 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tK 0, tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def Td147 : Tbl := [([tp 2 [L.K 0] [2, 1], tp 2 [L.K 0] [0, 1]], [tp 2 [L.K 0] [0, 1], tp 2 [L.K 0] [2, 1]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.C 0] [2, 1]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [0, 2]]),
  ([tp 2 [L.K 0] [0, 2], tK 0], [tK 0, tp 2 [L.K 0] [0, 2]]),
  ([tp 2 [L.K 0] [2, 1], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2], tp 2 [L.C 0] [2, 1]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.K 0] [2, 1]], [tp 2 [L.C 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.C 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]]),
  ([tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]]),
  ([tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 0]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 0]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]]),
  ([tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.K 0] [1, 0]]),
  ([tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.C 0] [1, 2]], [tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0], tp 2 [L.K 0] [1, 2], tp 2 [L.C 0] [1, 0]]),
  ([tp 2 [L.C 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1], tp 2 [L.K 0] [1, 0]]),
  ([tp 2 [L.K 0] [1, 0], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1], tp 2 [L.C 0] [1, 0]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.K 0] [2, 1], tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [2, 1]], [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 0]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]]),
  ([tp 2 [L.K 0] [1, 2], tp 2 [L.K 0] [1, 0]], [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 2]]),
  ([tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]]),
  ([tK 1, tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tC 1]),
  ([tp 2 [L.C 0] [0, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 0]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 0], tp 2 [L.K 0] [0, 2]]),
  ([tp 2 [L.K 0] [2, 0], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 2]], [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 2], tp 2 [L.C 0] [2, 0]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]], [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]]),
  ([tp 2 [L.C 0] [2, 1], tp 2 [L.K 0] [0, 2]], [tp 2 [L.K 0] [0, 2], tp 2 [L.C 0] [2, 1]]),
  ([tC 1, tK 0], [tK 0, tC 1])]

theorem rund147 : check 2 Td147 Ld147 Rd147
    [.sem 2 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tZ 2, tZ 1] 0,
    .sem 0 3 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1]] 0,
    .sem 6 1 [tp 2 [L.K 0] [0, 1]] 2,
    .rw 6 0 true,
    .sem 7 1 [tK 0] 2,
    .sem 4 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 7 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 6 2 [] 0,
    .sem 5 1 [tZ 2] 0,
    .sem 6 1 [tK 0] 2,
    .sw 5,
    .sem 6 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 5 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 6 0 [tS 1, tS 1] 0,
    .swp 7 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 7 1 [tZ 1] 0,
    .swp 4 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 5 2 [tp 2 [L.K 0] [2, 1], tZ 1] 0,
    .sem 7 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tH 0] 2,
    .sem 8 1 [tp 1 [L.H 0] [0]] 1,
    .sem 8 1 [tH 0] 1,
    .sem 9 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sem 15 1 [tp 1 [L.H 0] [0]] 1,
    .sem 8 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 9 1 [tH 0] 1,
    .sem 6 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tZ 1] 2,
    .sem 7 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tC 1, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 7 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .rw 6 1 true,
    .sem 6 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 8 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 7 2 true,
    .sem 7 1 [tC 1] 0,
    .sem 11 1 [tp 1 [L.H 0] [0]] 1,
    .sem 10 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sem 17 1 [tH 0] 1,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sem 11 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 10 1 [tp 1 [L.H 0] [0]] 1,
    .sem 10 1 [tH 0] 1,
    .sem 9 2 [tH 0, tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 10 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 11 1 [tH 2, tZ 2, tH 2, tZ 2, tH 2, tZ 2, tH 2] 0,
    .sem 18 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 21,
    .sw 22,
    .sw 23,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 21,
    .sw 22,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 21,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sem 18 7 [tp 1 [L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 11 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 7 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 7 2 false,
    .sem 8 1 [tC 1] 0,
    .sem 9 1 [tp 1 [L.H 0] [0]] 1,
    .sem 9 1 [tH 0] 1,
    .sem 10 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sem 16 1 [tp 1 [L.H 0] [0]] 1,
    .sem 9 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 10 1 [tH 0] 1,
    .sem 8 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tC 1] 0,
    .sw 9,
    .sem 10 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 10 2 false,
    .sem 11 1 [tC 1] 0,
    .sem 9 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tH 0] 2,
    .sw 10,
    .sem 6 0 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sw 12,
    .sem 8 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .rw 8 1 false,
    .rw 8 1 true,
    .sem 8 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .rw 7 3 false,
    .sem 12 1 [tp 1 [L.H 0] [0]] 1,
    .sem 11 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sem 18 1 [tH 0] 1,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sem 12 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 11 1 [tp 1 [L.H 0] [0]] 1,
    .sem 11 1 [tH 0] 1,
    .sem 11 1 [tp 1 [L.H 0] [0]] 1,
    .sem 10 1 [tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2] 0,
    .sem 23 1 [tH 0] 1,
    .sw 22,
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
    .sem 11 13 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 10 1 [tp 1 [L.H 0] [0]] 1,
    .sem 10 1 [tH 0] 1,
    .sem 11 4 [tZ 1, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sw 10,
    .sem 9 3 [tK 0, tZ 1] 2,
    .sem 6 0 [tZ 2, tp 2 [L.K 0] [0, 2], tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sem 9 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tZ 2] 0,
    .sem 10 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 10 1 [tZ 2] 0,
    .sem 11 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sem 17 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 10 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 11 1 [tZ 2] 0,
    .sem 11 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tZ 2] 0,
    .sw 12,
    .rw 8 4 false,
    .sem 10 1 [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1] 2,
    .swp 9 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 12 1 [tp 1 [L.H 0] [1]] 0,
    .swp 12 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) true,
    .sem 11 2 [] 2,
    .sem 10 1 [tK 1] 0,
    .sem 11 1 [tH 0] 1,
    .sw 10,
    .sem 11 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 10 1 [tp 1 [L.H 0] [0]] 1,
    .sem 11 0 [tS 0, tS 0] 2,
    .swp 12 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 9 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) false,
    .sem 9 1 [tH 1] 0,
    .swp 10 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 13 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 13 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) true,
    .sem 12 2 [] 2,
    .sem 11 1 [tK 1] 0,
    .sem 12 1 [tZ 0] 1,
    .sw 11,
    .sem 12 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 11 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 12 0 [tS 0, tS 0] 2,
    .swp 13 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 10 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) false,
    .sem 10 1 [tZ 1] 0,
    .swp 11 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 14 1 [tp 1 [L.H 0] [1]] 0,
    .swp 14 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) true,
    .sem 13 2 [] 2,
    .sem 12 1 [tK 1] 0,
    .sem 13 1 [tH 0] 1,
    .sw 12,
    .sem 13 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 12 1 [tp 1 [L.H 0] [0]] 1,
    .sem 13 0 [tS 0, tS 0] 2,
    .swp 14 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 11 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) false,
    .sem 11 1 [tH 1] 0,
    .rw 12 5 false,
    .swp 13 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 16 1 [tp 1 [L.H 0] [1]] 0,
    .swp 16 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) true,
    .sem 15 2 [] 2,
    .sem 14 1 [tK 1] 0,
    .sem 15 1 [tH 0] 1,
    .sw 14,
    .sem 15 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 14 1 [tp 1 [L.H 0] [0]] 1,
    .sem 15 0 [tS 0, tS 0] 2,
    .swp 16 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 13 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) false,
    .sem 13 1 [tH 1] 0,
    .swp 14 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 17 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 17 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) true,
    .sem 16 2 [] 2,
    .sem 15 1 [tK 1] 0,
    .sem 16 1 [tZ 0] 1,
    .sw 15,
    .sem 16 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 15 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 16 0 [tS 0, tS 0] 2,
    .swp 17 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 14 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) false,
    .sem 14 1 [tZ 1] 0,
    .swp 15 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 18 1 [tp 1 [L.H 0] [1]] 0,
    .swp 18 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) true,
    .sem 17 2 [] 2,
    .sem 16 1 [tK 1] 0,
    .sem 17 1 [tH 0] 1,
    .sw 16,
    .sem 17 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 16 1 [tp 1 [L.H 0] [0]] 1,
    .sem 17 0 [tS 0, tS 0] 2,
    .swp 18 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .swp 15 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) false,
    .sem 15 1 [tH 1] 0,
    .sem 9 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .rw 10 4 false,
    .sem 6 2 [tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sem 6 2 [tZ 2, tp 2 [L.K 0] [0, 2]] 1,
    .sem 6 2 [tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sem 6 2 [tZ 2, tp 2 [L.K 0] [0, 2]] 1,
    .sem 6 2 [tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sem 6 2 [tZ 2, tp 2 [L.K 0] [0, 2]] 1,
    .sem 8 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 7 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2], tp 2 [L.K 0] [2, 0]] 1,
    .sem 6 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2], tH 2] 1,
    .sem 6 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2]] 1,
    .rw 5 6 false,
    .sem 6 1 [tC 1] 0,
    .sem 5 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 4 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2], tp 2 [L.K 0] [2, 0]] 1,
    .sem 3 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2], tH 2] 1,
    .sem 3 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2]] 1,
    .rw 2 6 false,
    .sem 3 1 [tC 1] 0,
    .sem 2 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 4 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .sem 6 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .sem 3 1 [tp 2 [L.C 0] [2, 1]] 0,
    .sem 5 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 3 7 true,
    .sem 5 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 3 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 7 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2]] 1,
    .rw 6 6 false,
    .sem 6 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 7 1 [tC 1] 0,
    .sem 7 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tC 1] 0,
    .sem 8 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 8 2 false,
    .sem 9 1 [tC 1] 0,
    .sem 9 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tC 1] 0,
    .sem 8 1 [tK 0, tH 0] 2,
    .sem 9 1 [tp 1 [L.H 0] [0]] 1,
    .sem 9 1 [tH 0] 1,
    .sem 10 1 [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2] 0,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sw 15,
    .sem 16 1 [tp 1 [L.H 0] [0]] 1,
    .sem 9 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 10 1 [tH 0] 1,
    .rw 6 8 true,
    .rw 6 8 false,
    .sem 6 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 0]] 1,
    .rw 6 9 true,
    .sem 7 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .rw 7 10 true,
    .sem 8 2 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 9 10 true,
    .sem 10 2 [tZ 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 5 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 5 11 false,
    .sem 7 1 [tZ 1, tC 1] 0,
    .sem 11 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 10 1 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 17 1 [tZ 0] 1,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sem 11 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 10 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 10 1 [tZ 0] 1,
    .sem 11 1 [tC 1, tZ 1] 0,
    .sw 10,
    .swp 6 0 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]) true,
    .sem 9 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 9 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) true,
    .sem 8 2 [] 2,
    .sem 7 1 [tS 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tS 1] 0,
    .sem 16 1 [tZ 0] 1,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sem 8 9 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 1]] 0,
    .sem 7 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 0 [tS 0, tS 0] 2,
    .swp 9 0 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]) false,
    .swp 6 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) false,
    .sem 6 1 [tZ 1] 0,
    .sem 8 0 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 0]] 2,
    .rw 7 12 true,
    .sem 10 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 12 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 9 13 false,
    .sem 9 1 [tK 1] 0,
    .sem 10 1 [tC 0] 2,
    .sem 11 1 [tK 1] 0,
    .sem 12 1 [tC 0] 2,
    .sem 12 2 [tZ 0, tC 0] 2,
    .sw 11,
    .sem 10 2 [tZ 0, tC 0] 2,
    .sw 9,
    .sem 8 2 [tZ 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .sem 7 2 [tZ 0, tp 2 [L.K 0] [1, 0]] 2,
    .sw 6,
    .sem 6 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 5 1 [tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tS 1] 0,
    .sem 15 1 [tZ 0] 1,
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
    .sem 6 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 5 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 5 1 [tZ 0] 1,
    .sem 6 2 [tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 7 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]] 0,
    .rw 7 14 true,
    .sem 7 1 [tC 0] 2,
    .sem 8 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .rw 8 11 true,
    .sem 8 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 9 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 10 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .sem 11 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 10 15 true,
    .sem 11 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 11 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 12 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .sem 13 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 12 15 true,
    .sem 13 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 13 2 [tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sw 5,
    .sem 6 2 [tC 0, tZ 0] 2,
    .sem 7 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2], tZ 0] 1,
    .sem 8 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tZ 0] 1,
    .sem 9 1 [tS 1, tK 1, tS 1] 0,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 9 1 [tZ 0] 1,
    .sem 9 2 [tp 2 [L.K 0] [1, 0], tZ 0] 2,
    .sem 10 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 10 1 [tZ 0] 1,
    .sem 11 1 [tS 1, tK 1, tS 1] 0,
    .sw 10,
    .sw 11,
    .sw 12,
    .sem 13 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 10 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 11 1 [tZ 0] 1,
    .sem 11 2 [tp 2 [L.K 0] [1, 0], tZ 0] 2,
    .sem 7 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 7 16 false,
    .sem 10 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 11 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 0]] 2,
    .sem 10 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 10 17 false,
    .sem 11 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 10 1 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 11 2 [tZ 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .swp 12 0 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]) true,
    .sem 15 1 [tp 1 [L.H 0] [1]] 0,
    .swp 15 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) true,
    .sem 14 2 [] 2,
    .sem 13 1 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 20 1 [tH 0] 1,
    .sw 19,
    .sw 18,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sem 14 7 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 13 1 [tp 1 [L.H 0] [0]] 1,
    .sem 14 0 [tS 0, tS 0] 2,
    .swp 15 0 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]) false,
    .swp 12 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) false,
    .sem 12 1 [tH 1] 0,
    .sem 10 2 [tZ 0, tp 2 [L.K 0] [1, 0]] 2,
    .sem 10 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 9 1 [tS 1, tK 1, tS 1] 0,
    .sem 12 1 [tZ 0] 1,
    .sw 11,
    .sw 10,
    .sw 9,
    .sem 10 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 9 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 9 1 [tZ 0] 1,
    .sem 8 2 [tZ 0, tp 2 [L.K 0] [1, 0]] 2,
    .sem 8 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 7 1 [tS 1, tK 1, tS 1] 0,
    .sem 10 1 [tZ 0] 1,
    .sw 9,
    .sw 8,
    .sw 7,
    .sem 8 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 7 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 7 1 [tZ 0] 1,
    .sem 6 2 [tZ 0, tC 0] 2,
    .sw 5,
    .sem 5 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 4 1 [tS 1, tK 1, tS 1] 0,
    .sem 7 1 [tZ 0] 1,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 4 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 4 1 [tZ 0] 1,
    .sem 3 2 [tZ 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 13 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 13 11 false,
    .sem 12 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tZ 1] 0,
    .sem 12 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .rw 11 15 false,
    .sem 11 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 12 1 [tC 0] 2,
    .sem 10 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tK 1] 0,
    .sem 10 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .rw 9 15 false,
    .sem 9 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 10 1 [tC 0] 2,
    .sem 8 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tK 1] 0,
    .sem 7 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 8 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]] 0,
    .rw 7 14 false,
    .sem 7 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 6 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tZ 1] 0,
    .sem 5 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tK 1] 0,
    .sem 4 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 4 11 false,
    .sem 3 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 3 1 [tZ 0] 1,
    .sem 4 1 [tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tS 1] 0,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sem 13 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 3 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 4 1 [tZ 0] 1,
    .sem 4 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0], tZ 0] 1,
    .sw 5,
    .sw 6,
    .sem 7 2 [tp 2 [L.K 0] [1, 0], tZ 0] 2,
    .sw 8,
    .sem 9 2 [tC 0, tZ 0] 2,
    .sw 10,
    .sem 11 2 [tC 0, tZ 0] 2,
    .sem 8 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 9 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 10 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 11 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 8 13 true,
    .sem 11 1 [tC 1] 0,
    .sem 9 1 [tC 1] 0,
    .sem 7 2 [] 2,
    .sem 6 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sw 8,
    .sem 9 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 8 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tZ 0] 1,
    .sem 9 1 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sw 12,
    .sw 13,
    .sw 14,
    .sem 15 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 9 1 [tZ 0] 1,
    .sem 5 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 1] 0,
    .sem 6 1 [tp 2 [L.K 0] [1, 2]] 0,
    .rw 6 18 false,
    .sem 7 1 [tK 1] 0,
    .sem 7 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 1] 0,
    .sw 8,
    .sem 5 1 [tZ 1, tC 1] 0,
    .sem 9 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sem 15 1 [tZ 0] 1,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sem 9 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 8 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tZ 0] 1,
    .sem 9 1 [tC 1, tZ 1] 0,
    .sw 8,
    .swp 4 0 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]) true,
    .sem 7 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 7 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) true,
    .sem 6 2 [] 2,
    .sem 5 1 [tS 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tS 1] 0,
    .sem 14 1 [tZ 0] 1,
    .sw 13,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sem 6 9 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 1]] 0,
    .sem 5 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 6 0 [tS 0, tS 0] 2,
    .swp 7 0 (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 1]) (tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]) false,
    .swp 4 0 (tp 1 [L.Z 0] [0]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 1 [tZ 1] 0,
    .sem 6 0 [tp 2 [L.K 0] [1, 0], tp 2 [L.K 0] [1, 0]] 2,
    .rw 5 12 true,
    .sem 8 1 [tp 2 [L.C 0] [1, 2]] 0,
    .sem 10 1 [tp 2 [L.C 0] [1, 2]] 0,
    .rw 7 13 false,
    .sem 7 1 [tK 1] 0,
    .sem 8 1 [tC 0] 2,
    .sem 9 1 [tK 1] 0,
    .sem 10 1 [tC 0] 2,
    .sem 10 2 [tZ 0, tC 0] 2,
    .sw 9,
    .sem 8 2 [tZ 0, tC 0] 2,
    .sw 7,
    .sem 6 2 [tZ 0, tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .sem 5 2 [tZ 0, tp 2 [L.K 0] [1, 0]] 2,
    .sw 4,
    .sem 4 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 3 1 [tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tS 1] 0,
    .sem 13 1 [tZ 0] 1,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sw 3,
    .sem 4 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 3 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 3 1 [tZ 0] 1,
    .sem 4 2 [tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 5 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]] 0,
    .rw 5 14 true,
    .sem 5 1 [tC 0] 2,
    .sem 6 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .rw 6 11 true,
    .sem 6 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 7 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 8 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .sem 9 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 8 15 true,
    .sem 9 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 9 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 10 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .sem 11 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 10 15 true,
    .sem 11 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 11 2 [tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 12 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .rw 13 11 true,
    .sem 13 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sw 3,
    .sem 4 2 [tC 0, tZ 0] 2,
    .sem 5 2 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2], tZ 0] 1,
    .sem 6 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 6 1 [tZ 0] 1,
    .sem 7 1 [tS 1, tK 1, tS 1] 0,
    .sw 6,
    .sw 7,
    .sw 8,
    .sem 9 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 6 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 7 1 [tZ 0] 1,
    .sem 7 2 [tp 2 [L.K 0] [1, 0], tZ 0] 2,
    .sem 8 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tZ 0] 1,
    .sem 9 1 [tS 1, tK 1, tS 1] 0,
    .sw 8,
    .sw 9,
    .sw 10,
    .sem 11 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 9 1 [tZ 0] 1,
    .sem 9 2 [tp 2 [L.K 0] [1, 0], tZ 0] 2,
    .sw 10,
    .sem 5 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 5 16 false,
    .sem 8 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 10 2 [tZ 0, tH 1] 2,
    .sem 9 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1, L.H 1, L.Z 1, L.H 1] [1, 0]] 2,
    .sem 8 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 8 17 false,
    .sem 9 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .sem 8 1 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 9 2 [tZ 0, tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]] 1,
    .swp 10 0 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]) true,
    .sem 13 1 [tp 1 [L.H 0] [1]] 0,
    .swp 13 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) true,
    .sem 12 2 [] 2,
    .sem 11 1 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 18 1 [tH 0] 1,
    .sw 17,
    .sw 16,
    .sw 15,
    .sw 14,
    .sw 13,
    .sw 12,
    .sw 11,
    .sem 12 7 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 11 1 [tp 1 [L.H 0] [0]] 1,
    .sem 12 0 [tS 0, tS 0] 2,
    .swp 13 0 (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]) (tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [0, 2]) false,
    .swp 10 0 (tp 1 [L.H 0] [0]) (tp 1 [L.H 0] [1]) false,
    .sem 10 1 [tH 1] 0,
    .rw 14 19 true,
    .rw 15 8 true,
    .sem 14 2 [] 2,
    .sem 15 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 15 20 true,
    .sem 14 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 16 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 11 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .sem 13 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [2, 0]] 1,
    .rw 11 7 false,
    .sem 11 1 [tC 1] 0,
    .sem 13 1 [tC 1] 0,
    .sem 16 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 0]] 2,
    .rw 16 21 true,
    .sem 15 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [1, 2]] 0,
    .sem 16 1 [tp 2 [L.C 0] [2, 0]] 1,
    .rw 15 22 true,
    .sem 16 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 17 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 14 2 [tH 2] 1,
    .rw 2 8 true,
    .sem 10 2 [tH 1, tZ 0] 2,
    .sem 16 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]] 0,
    .sem 17 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 0]] 2,
    .rw 16 9 false,
    .sem 16 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .rw 16 8 true,
    .rw 16 8 false,
    .sw 10,
    .sem 9 2 [tZ 0, tp 2 [L.K 0] [1, 0]] 2,
    .sem 9 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tS 1, tK 1, tS 1] 0,
    .sem 11 1 [tZ 0] 1,
    .sw 10,
    .sw 9,
    .sw 8,
    .sem 9 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 8 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 8 1 [tZ 0] 1,
    .sem 7 2 [tZ 0, tp 2 [L.K 0] [1, 0]] 2,
    .sem 7 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 6 1 [tS 1, tK 1, tS 1] 0,
    .sem 9 1 [tZ 0] 1,
    .sw 8,
    .sw 7,
    .sw 6,
    .sem 7 3 [tp 2 [L.K 0] [2, 1]] 0,
    .sem 6 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 6 1 [tZ 0] 1,
    .sem 5 2 [tZ 0, tC 0] 2,
    .sw 4,
    .sem 4 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 3 1 [tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tK 1, tH 2, tZ 1, tS 1] 0,
    .sem 13 1 [tZ 0] 1,
    .sw 12,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 4,
    .sw 3,
    .sem 4 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 3 1 [tp 1 [L.Z 0] [0]] 1,
    .sem 3 1 [tZ 0] 1,
    .sem 4 2 [tZ 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 5 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [2, 1]] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 5 15 true,
    .sem 6 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 6 2 [tK 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 7 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]] 0,
    .rw 7 14 true,
    .sem 7 1 [tC 0] 2,
    .sem 8 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 8 2 [tK 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 9 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [2, 1]] 0,
    .rw 9 14 true,
    .sem 9 1 [tC 0] 2,
    .sem 10 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sem 10 2 [tZ 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .sw 3,
    .sem 4 2 [tp 2 [L.K 0] [1, 0], tZ 0] 2,
    .sw 5,
    .sem 6 2 [tC 0, tZ 0] 2,
    .sw 7,
    .sem 8 2 [tC 0, tZ 0] 2,
    .sem 5 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 6 1 [tp 2 [L.C 0] [1, 0]] 2,
    .sem 7 1 [tp 2 [L.K 0] [1, 2]] 0,
    .sem 8 1 [tp 2 [L.C 0] [1, 0]] 2,
    .rw 5 13 true,
    .sem 8 1 [tC 1] 0,
    .sem 6 1 [tC 1] 0,
    .sem 4 2 [] 2,
    .sem 2 2 [tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 3 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 3 20 true,
    .sem 4 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 2 [tK 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 5 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 5 20 true,
    .sem 6 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 2 [tH 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 7 2 [tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 6 2 [tH 1, tH 0] 2,
    .rw 8 8 false,
    .sem 10 1 [tH 2, tp 2 [L.K 0] [2, 0]] 1,
    .sem 2 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sw 5,
    .sw 4,
    .sem 3 2 [tH 0, tK 0] 2,
    .sem 3 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 4 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 1 2 [] 0,
    .sw 10,
    .sem 3 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2]] 1,
    .sem 4 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 3 6 true,
    .sem 4 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 4 2 [tZ 2, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 5 2 [tp 2 [L.K 0] [0, 2], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 6 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 2]] 1,
    .sem 7 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 6 6 true,
    .sem 7 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 7 2 [tZ 2, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 1,
    .sem 7 4 [] 1,
    .sem 7 2 [tZ 1, tK 0] 2,
    .sem 6 2 [tZ 1, tp 2 [L.K 0] [2, 1]] 0,
    .sem 4 2 [tp 2 [L.K 0] [0, 2], tZ 2] 1,
    .sw 5,
    .rw 0 23 false,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 2 2 [tp 2 [L.K 0] [2, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 3 1 [tH 1, tZ 1, tH 1, tC 1, tH 1, tZ 1, tH 1] 0,
    .sem 9 1 [tp 1 [L.H 0] [1]] 0,
    .swp 9 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) true,
    .swp 12 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 11 2 [] 0,
    .sem 10 1 [tH 2] 0,
    .sem 11 1 [tK 0] 2,
    .sw 10,
    .sem 11 1 [tp 1 [L.H 0] [2]] 0,
    .sem 10 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 11 0 [tS 1, tS 1] 0,
    .swp 12 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) false,
    .sem 12 1 [tH 1] 0,
    .swp 9 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 8 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 8 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 11 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 10 2 [] 0,
    .sem 9 1 [tZ 2] 0,
    .sem 10 1 [tK 0] 2,
    .sw 9,
    .sem 10 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 9 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 10 0 [tS 1, tS 1] 0,
    .swp 11 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 11 1 [tZ 1] 0,
    .swp 8 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 7 1 [tp 1 [L.H 0] [1]] 0,
    .swp 7 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) true,
    .swp 10 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 9 2 [] 0,
    .sem 8 1 [tH 2] 0,
    .sem 9 1 [tK 0] 2,
    .sw 8,
    .sem 9 1 [tp 1 [L.H 0] [2]] 0,
    .sem 8 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 9 0 [tS 1, tS 1] 0,
    .swp 10 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) false,
    .sem 10 1 [tH 1] 0,
    .swp 7 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 6 1 [tp 2 [L.C 0] [2, 1]] 0,
    .rw 6 24 false,
    .sem 7 1 [tC 1] 0,
    .sem 5 1 [tp 1 [L.H 0] [1]] 0,
    .swp 5 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) true,
    .swp 8 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 7 2 [] 0,
    .sem 6 1 [tH 2] 0,
    .sem 7 1 [tK 0] 2,
    .sw 6,
    .sem 7 1 [tp 1 [L.H 0] [2]] 0,
    .sem 6 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 7 0 [tS 1, tS 1] 0,
    .swp 8 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) false,
    .sem 8 1 [tH 1] 0,
    .swp 5 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 4 1 [tp 1 [L.Z 0] [1]] 0,
    .swp 4 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) true,
    .swp 7 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 6 2 [] 0,
    .sem 5 1 [tZ 2] 0,
    .sem 6 1 [tK 0] 2,
    .sw 5,
    .sem 6 1 [tp 1 [L.Z 0] [2]] 0,
    .sem 5 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 6 0 [tS 1, tS 1] 0,
    .swp 7 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 7 1 [tZ 1] 0,
    .swp 4 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 3 1 [tp 1 [L.H 0] [1]] 0,
    .swp 3 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) true,
    .swp 6 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) true,
    .sem 5 2 [] 0,
    .sem 4 1 [tH 2] 0,
    .sem 5 1 [tK 0] 2,
    .sw 4,
    .sem 5 1 [tp 1 [L.H 0] [2]] 0,
    .sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .sem 5 0 [tS 1, tS 1] 0,
    .swp 6 1 (tp 1 [L.H 0] [2]) (tp 1 [L.H 0] [1]) false,
    .sem 6 1 [tH 1] 0,
    .swp 3 1 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 4 7 [tp 2 [L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0] [1, 2]] 0,
    .sem 4 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 6 1 [tp 2 [L.K 0] [0, 1]] 2,
    .rw 5 0 false,
    .sem 5 1 [tK 0] 2,
    .sem 4 1 [tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2] 0,
    .sw 10,
    .sw 9,
    .sw 8,
    .rw 7 25 false,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .rw 3 5 false] = true := by
  decide +kernel

theorem td147 (ih : IH 3) : Derivable (theory 3) (wcT 3 Ld147) (wcT 3 Rd147) :=
  check_sound ih (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (td133 ih)) (AllD.cons (te13f2f1 ih) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (td132 ih)) (AllD.cons (td146 ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (td134 ih)) (AllD.cons (td135 ih) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (te18i ih)) (AllD.cons (rel_entry havailNone [0, 1] (by decide +kernel) (te14if1 ih)) (AllD.cons (td130 ih) (AllD.cons (rel_entry havailNone [0, 1, 0] (by decide +kernel) (td130 ih)) (AllD.cons (te18f2 ih) (AllD.cons (rel_entry havailNone [1, 0] (by decide +kernel) (te18f2 ih)) (AllD.cons (rel_entry havailNone [0, 1, 0] (by decide +kernel) (td134 ih)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te14 ih)) (AllD.cons (rel_entry havailNone [0, 1, 0] (by decide +kernel) (te18 ih)) (AllD.cons (rel_entry havailNone [0, 1, 0] (by decide +kernel) (te18i ih)) (AllD.cons (rel_entry havailNone [0, 1, 0] (by decide +kernel) (te17 ih)) (AllD.cons (rel_entry havailNone [1, 0] (by decide +kernel) (td132f2 ih)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (td135 ih)) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (td130 ih)) (AllD.cons (te18i ih) (AllD.cons (rel_entry havailNone [0] (by decide +kernel) (te18 ih)) (AllD.cons (rel_entry havailNone [1, 0] (by decide +kernel) (te18i ih)) (AllD.cons (te13f1 ih) (AllD.cons (rel_entry havailNone [1] (by decide +kernel) (te13 ih)) (AllD.cons (te13 ih) (AllD.nil 3))))))))))))))))))))))))))) rund147

def LBridgeLd139 : List Tk := [tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tS 0, tH 2, tZ 2, tH 2]

def RBridgeLd139 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TBridgeLd139 : Tbl := []

theorem runBridgeLd139 : check 2 TBridgeLd139 LBridgeLd139 RBridgeLd139
    [.sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 8 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 7 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 10 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 9 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 11 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 1 [tH 2, tZ 2, tH 2] 0,
    .sem 7 1 [tS 0, tK 0, tS 0] 2,
    .sw 6,
    .sw 5,
    .sw 4,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 8,
    .sw 7,
    .sw 6,
    .sem 7 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 9 2 [] 2,
    .sem 5 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 6 1 [tH 2, tZ 2, tH 2] 0,
    .sem 9 1 [tS 0, tK 0, tS 0] 2,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 9,
    .sw 8,
    .sw 7,
    .sw 10,
    .sw 9,
    .sw 8,
    .sem 9 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 6 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 7 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 2 [] 0] = true := by
  decide +kernel

theorem tBridgeLd139 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd139) (wcT 3 RBridgeLd139) :=
  check_sound ih (AllD.nil 3) runBridgeLd139

def LBridgeRd139 : List Tk := [tH 2, tZ 2, tH 2, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tS 0, tH 2, tZ 2, tH 2, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0]

def RBridgeRd139 : List Tk := [tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]]

def TBridgeRd139 : Tbl := []

theorem runBridgeRd139 : check 2 TBridgeRd139 LBridgeRd139 RBridgeRd139
    [.sem 4 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 3 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 6 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 5 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 14 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 13 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 16 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 15 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 7 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 1 [tH 2, tZ 2, tH 2] 0,
    .sem 3 1 [tS 0, tK 0, tS 0] 2,
    .sw 2,
    .sw 1,
    .sw 0,
    .sw 3,
    .sw 2,
    .sw 1,
    .sw 4,
    .sw 3,
    .sw 2,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 5 2 [] 2,
    .sem 1 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 1 [tH 2, tZ 2, tH 2] 0,
    .sem 5 1 [tS 0, tK 0, tS 0] 2,
    .sw 4,
    .sw 3,
    .sw 2,
    .sw 5,
    .sw 4,
    .sw 3,
    .sw 6,
    .sw 5,
    .sw 4,
    .sem 5 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 3 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 2 [] 0] = true := by
  decide +kernel

theorem tBridgeRd139 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd139) (wcT 3 RBridgeRd139) :=
  check_sound ih (AllD.nil 3) runBridgeRd139

theorem e139 (ih : IH 3) : Derivable (theory 3) l139 r139 := by
  have hl : l139 = wcT 3 LBridgeLd139 := circW_eq_wcT 3 _
  have hr : r139 = wcT 3 LBridgeRd139 := circW_eq_wcT 3 _
  rw [hl, hr]
  exact (tBridgeLd139 ih).trans ((td139 ih).trans (tBridgeRd139 ih).symm)

def LBridgeLd140 : List Tk := [tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tH 2, tZ 2, tH 2, tS 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tH 2, tZ 2, tH 2]

def RBridgeLd140 : List Tk := [tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0]]

def TBridgeLd140 : Tbl := []

theorem runBridgeLd140 : check 2 TBridgeLd140 LBridgeLd140 RBridgeLd140
    [.sem 2 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 1 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 4 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 3 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 9 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 8 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 11 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 10 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 9 0 [tS 0, tS 0] 2,
    .swp 7 0 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [1, 2]) false,
    .sem 10 0 [tS 0, tS 0] 2,
    .sem 9 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 8 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 11 0 [tS 0, tS 0] 2,
    .swp 9 0 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [1, 2]) false,
    .sem 11 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 10 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 9 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 1 [tS 0, tK 0, tS 0] 2,
    .sem 11 1 [tH 2, tZ 2, tH 2] 0,
    .sw 10,
    .sw 9,
    .sw 8,
    .sw 11,
    .sw 10,
    .sw 9,
    .sw 12,
    .sw 11,
    .sw 10,
    .sem 11 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 1 [tH 2, tZ 2, tH 2] 0,
    .sem 8 1 [tS 0, tK 0, tS 0] 2,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 8,
    .sw 7,
    .sw 6,
    .sw 9,
    .sw 8,
    .sw 7,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 6 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 7 2 [] 0] = true := by
  decide +kernel

theorem tBridgeLd140 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd140) (wcT 3 RBridgeLd140) :=
  check_sound ih (AllD.nil 3) runBridgeLd140

def LBridgeRd140 : List Tk := [tH 2, tZ 2, tH 2, tS 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tH 2, tZ 2, tH 2, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0]

def RBridgeRd140 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [1, 0], tK 0, tp 2 [L.C 0] [0, 2], tK 0, tp 2 [L.C 0] [0, 2]]

def TBridgeRd140 : Tbl := []

theorem runBridgeRd140 : check 2 TBridgeRd140 LBridgeRd140 RBridgeRd140
    [.sem 5 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 4 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 7 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 6 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 14 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 13 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 16 1 [tp 2 [L.C 0] [1, 2]] 0,
    .swp 15 0 (tp 2 [L.C 0] [1, 2]) (tp 2 [L.C 0] [0, 2]) false,
    .sem 5 0 [tS 0, tS 0] 2,
    .swp 3 0 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [1, 2]) false,
    .sem 6 0 [tS 0, tS 0] 2,
    .sem 5 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 4 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 7 0 [tS 0, tS 0] 2,
    .swp 5 0 (tp 2 [L.C 0] [0, 2]) (tp 2 [L.C 0] [1, 2]) false,
    .sem 7 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 6 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 1 [tS 0, tK 0, tS 0] 2,
    .sem 7 1 [tH 2, tZ 2, tH 2] 0,
    .sw 6,
    .sw 5,
    .sw 4,
    .sw 7,
    .sw 6,
    .sw 5,
    .sw 8,
    .sw 7,
    .sw 6,
    .sem 7 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 1 [tH 2, tZ 2, tH 2] 0,
    .sem 4 1 [tS 0, tK 0, tS 0] 2,
    .sw 3,
    .sw 2,
    .sw 1,
    .sw 4,
    .sw 3,
    .sw 2,
    .sw 5,
    .sw 4,
    .sw 3,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 1 3 [tp 2 [L.K 0] [1, 0]] 2,
    .sem 2 2 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 2 [] 0] = true := by
  decide +kernel

theorem tBridgeRd140 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd140) (wcT 3 RBridgeRd140) :=
  check_sound ih (AllD.nil 3) runBridgeRd140

theorem e140 (ih : IH 3) : Derivable (theory 3) l140 r140 := by
  have hl : l140 = wcT 3 LBridgeLd140 := circW_eq_wcT 3 _
  have hr : r140 = wcT 3 LBridgeRd140 := circW_eq_wcT 3 _
  rw [hl, hr]
  exact (tBridgeLd140 ih).trans ((td140 ih).trans (tBridgeRd140 ih).symm)

def LBridgeLd145 : List Tk := [tS 0, tK 0, tS 0, tC 0, tK 1, tS 1, tZ 2, tS 1, tK 1, tS 1, tZ 2, tS 1]

def RBridgeLd145 : List Tk := [tp 2 [L.K 0] [1, 0], tC 0, tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2]]

def TBridgeLd145 : Tbl := []

theorem runBridgeLd145 : check 2 TBridgeLd145 LBridgeLd145 RBridgeLd145
    [.sem 1 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 0 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 6 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 5 1 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [2, 1]) false,
    .sem 5 0 [tS 1, tS 1] 0,
    .sem 4 1 [tp 1 [L.Z 0] [2]] 0,
    .swp 3 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 6 0 [tS 1, tS 1] 0,
    .swp 4 1 (tp 2 [L.K 0] [2, 1]) (tp 2 [L.K 0] [1, 2]) false,
    .sem 6 1 [tp 1 [L.Z 0] [2]] 0,
    .swp 5 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 2 4 [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tBridgeLd145 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd145) (wcT 3 RBridgeLd145) :=
  check_sound ih (AllD.nil 3) runBridgeLd145

def LBridgeRd145 : List Tk := [tK 1, tS 1, tZ 2, tS 1, tK 1, tS 1, tZ 2, tS 1, tS 0, tK 0, tS 0, tC 0]

def RBridgeRd145 : List Tk := [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2], tp 2 [L.K 0] [1, 0], tC 0]

def TBridgeRd145 : Tbl := []

theorem runBridgeRd145 : check 2 TBridgeRd145 LBridgeRd145 RBridgeRd145
    [.sem 4 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 3 1 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [2, 1]) false,
    .sem 7 1 [tp 2 [L.K 0] [0, 1]] 2,
    .swp 6 0 (tp 2 [L.K 0] [0, 1]) (tp 2 [L.K 0] [1, 0]) false,
    .sem 3 0 [tS 1, tS 1] 0,
    .sem 2 1 [tp 1 [L.Z 0] [2]] 0,
    .swp 1 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 4 0 [tS 1, tS 1] 0,
    .swp 2 1 (tp 2 [L.K 0] [2, 1]) (tp 2 [L.K 0] [1, 2]) false,
    .sem 4 1 [tp 1 [L.Z 0] [2]] 0,
    .swp 3 1 (tp 1 [L.Z 0] [2]) (tp 1 [L.Z 0] [1]) false,
    .sem 0 4 [tp 2 [L.K 0, L.S 0, L.Z 1, L.S 0, L.K 0, L.S 0, L.Z 1, L.S 0] [1, 2]] 0] = true := by
  decide +kernel

theorem tBridgeRd145 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd145) (wcT 3 RBridgeRd145) :=
  check_sound ih (AllD.nil 3) runBridgeRd145

theorem e145 (ih : IH 3) : Derivable (theory 3) l145 r145 := by
  have hl : l145 = wcT 3 LBridgeLd145 := circW_eq_wcT 3 _
  have hr : r145 = wcT 3 LBridgeRd145 := circW_eq_wcT 3 _
  rw [hl, hr]
  exact (tBridgeLd145 ih).trans ((td145 ih).trans (tBridgeRd145 ih).symm)

def LBridgeLd146 : List Tk := [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1]

def RBridgeLd146 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def TBridgeLd146 : Tbl := []

theorem runBridgeLd146 : check 2 TBridgeLd146 LBridgeLd146 RBridgeLd146
    [.sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 6 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 7 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 10 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 11 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 13 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 14 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 16 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 1 5 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 3 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 4 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2] = true := by
  decide +kernel

theorem tBridgeLd146 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd146) (wcT 3 RBridgeLd146) :=
  check_sound ih (AllD.nil 3) runBridgeLd146

def LBridgeRd146 : List Tk := [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tC 1, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2]

def RBridgeRd146 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TBridgeRd146 : Tbl := []

theorem runBridgeRd146 : check 2 TBridgeRd146 LBridgeRd146 RBridgeRd146
    [.sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 6 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 8 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 9 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 10 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 12 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 13 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 14 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 16 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 3 8 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tBridgeRd146 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd146) (wcT 3 RBridgeRd146) :=
  check_sound ih (AllD.nil 3) runBridgeRd146

theorem e146 (ih : IH 3) : Derivable (theory 3) l146 r146 := by
  have hl : l146 = wcT 3 LBridgeLd146 := circW_eq_wcT 3 _
  have hr : r146 = wcT 3 LBridgeRd146 := circW_eq_wcT 3 _
  rw [hl, hr]
  exact (tBridgeLd146 ih).trans ((td146 ih).trans (tBridgeRd146 ih).symm)

def LBridgeLd147 : List Tk := [tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tS 1, tK 1, tS 1, tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2, tS 0, tK 1, tS 0, tK 0, tS 1, tK 1, tS 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1]

def RBridgeLd147 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [0, 2], tK 0, tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]]

def TBridgeLd147 : Tbl := []

theorem runBridgeLd147 : check 2 TBridgeLd147 LBridgeLd147 RBridgeLd147
    [.sem 8 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 7 1 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [2, 1]) false,
    .sem 16 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 15 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 18 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 17 1 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [2, 1]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 4 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 6 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 10 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 12 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 13 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 15 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 2 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 6 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 7 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2] = true := by
  decide +kernel

theorem tBridgeLd147 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeLd147) (wcT 3 RBridgeLd147) :=
  check_sound ih (AllD.nil 3) runBridgeLd147

def LBridgeRd147 : List Tk := [tH 1, tZ 1, tH 1, tK 0, tH 1, tZ 1, tH 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2, tS 1, tK 1, tS 1, tK 0, tS 0, tK 1, tS 0, tH 2, tZ 2, tH 2, tC 1, tH 2, tZ 2, tH 2, tS 1, tK 1, tS 1, tH 2, tZ 2, tH 2, tK 1, tH 2, tZ 2, tH 2]

def RBridgeRd147 : List Tk := [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tK 0, tp 2 [L.K 0] [0, 2], tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]]

def TBridgeRd147 : Tbl := []

theorem runBridgeRd147 : check 2 TBridgeRd147 LBridgeRd147 RBridgeRd147
    [.sem 15 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 14 1 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [2, 1]) false,
    .sem 17 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 16 0 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [0, 2]) false,
    .sem 25 1 [tp 2 [L.K 0] [1, 2]] 0,
    .swp 24 1 (tp 2 [L.K 0] [1, 2]) (tp 2 [L.K 0] [2, 1]) false,
    .sem 0 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 2 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .sem 3 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 9 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 11 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 13 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 15 3 [tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [0, 1]] 2,
    .sem 1 3 [tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0,
    .sem 5 7 [tp 2 [L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1] [1, 2], tp 2 [L.K 0] [2, 1], tp 2 [L.H 1, L.Z 1, L.H 1, L.K 0, L.H 1, L.Z 1, L.H 1] [1, 2]] 0] = true := by
  decide +kernel

theorem tBridgeRd147 (ih : IH 3) : Derivable (theory 3) (wcT 3 LBridgeRd147) (wcT 3 RBridgeRd147) :=
  check_sound ih (AllD.nil 3) runBridgeRd147

theorem e147 (ih : IH 3) : Derivable (theory 3) l147 r147 := by
  have hl : l147 = wcT 3 LBridgeLd147 := circW_eq_wcT 3 _
  have hr : r147 = wcT 3 LBridgeRd147 := circW_eq_wcT 3 _
  rw [hl, hr]
  exact (tBridgeLd147 ih).trans ((td147 ih).trans (tBridgeRd147 ih).symm)

end QCert.RealCliffordCH.Sec8.D.W3T
