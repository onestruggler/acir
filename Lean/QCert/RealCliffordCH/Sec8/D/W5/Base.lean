/- Five-wire certificates reconstructed from Appendix D.4. -/
import QCert.RealCliffordCH.Sec8.D.W3.Sym
import QCert.RealCliffordCH.Sec8.D.N8.Anchors
import Mathlib.Tactic.IntervalCases

namespace QCert.RealCliffordCH.Sec8.D.W5T
open Circuit WE WS Net
open Eng (L)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev tH (j : Nat) : Tk := Tk.s (L.H j)
abbrev tZ (j : Nat) : Tk := Tk.s (L.Z j)
abbrev tC (j : Nat) : Tk := Tk.s (L.C j)
abbrev tK (j : Nat) : Tk := Tk.s (L.K j)
abbrev tS (j : Nat) : Tk := Tk.s (L.S j)
abbrev tg (Kd : Kind) (tg : List Nat) (cs : List (Nat × Bool)) : Tk := Tk.g Kd tg cs
abbrev tp (m : Nat) (w : List L) (ps : List Nat) : Tk := Tk.p m w ps

theorem havail (ih : IH 5) : ∀ K k, decide (k + kindSp K < 5) = true → CanonSym K k := by
  intro K k h
  simp only [decide_eq_true_eq] at h
  cases K <;> simp only [kindSp] at h
  all_goals
    have hk : k < 4 := by omega
    interval_cases k <;> first | omega | exact canonSym_small ih _ _ (by simp [kindSp]) (by decide +kernel)

theorem rule19 : Derivable (theory 5)
    (wcT 5 [tZ 0, tg .box [0] [(4, true), (3, true), (2, true), (1, true)]])
    (wcT 5 [tg .box [0] [(4, true), (3, true), (2, true), (1, true)], tZ 0]) := by
  exact N8.t19 0
def L249Base0 : List Tk := [tC 0, tg .box [1] [(4, true), (3, true), (2, true)]]

def R249Base0 : List Tk := [tg .box [1] [(4, true), (3, true), (2, true)], tC 0]

def T249Base0 : Tbl := [([tS 0, tg .xz [2] [(1, true), (0, true)], tS 0], [tg .xz [2] [(0, true), (1, true)]]),
  ([tS 0, tg .zx [2] [(1, true), (0, true)], tS 0], [tg .zx [2] [(0, true), (1, true)]]),
  ([tS 1, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tS 0, tS 1, tS 0, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 0, tS 1, tS 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tS 1, tS 0, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 0, tS 1, tS 0, tS 0, tS 1], [tg .box [2] [(4, true), (3, true), (1, true), (0, true)]]),
  ([tp 1 [L.Z 0] [2], tg .box [2] [(4, true), (3, true), (1, true), (0, true)]], [tg .box [2] [(4, true), (3, true), (1, true), (0, true)], tp 1 [L.Z 0] [2]])]

theorem run249Base0 : check 4 T249Base0 L249Base0 R249Base0
    [.sem 0 0 [tZ 2, tg .xz [2] [(1, true), (0, true)], tg .zx [2] [(1, true), (0, true)], tZ 2] 3,
    .sem 6 0 [tg .xz [2] [(1, true), (0, true)], tg .zx [2] [(1, true), (0, true)]] 3,
    .sem 7 0 [tg .box [1] [(4, true), (3, true), (2, true)], tg .box [1] [(4, true), (3, true), (2, true)]] 0,
    .sem 2 3 [tZ 2, tg .zx [2] [(1, true), (0, true)]] 3,
    .sem 3 1 [tg .zx [2] [(0, true), (1, true)]] 3,
    .sem 5 1 [tg .xz [2] [(0, true), (1, true)]] 3,
    .swp 6 0 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [1] [(4, true), (3, true), (2, true)]) true,
    .rw 5 0 true,
    .swp 4 0 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [1] [(4, true), (3, true), (2, true)]) true,
    .rw 3 1 true,
    .sem 11 2 [] 2,
    .sem 8 2 [] 2,
    .sem 5 2 [] 2,
    .swp 7 1 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) true,
    .swp 8 0 (tg .box [1] [(4, true), (3, true), (0, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) true,
    .swp 6 1 (tg .xz [1] [(2, true), (0, true)]) (tg .xz [2] [(1, true), (0, true)]) true,
    .swp 7 0 (tg .xz [0] [(2, true), (1, true)]) (tg .xz [1] [(2, true), (0, true)]) true,
    .swp 5 1 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) true,
    .swp 6 0 (tg .box [1] [(4, true), (3, true), (0, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) true,
    .swp 4 1 (tg .zx [1] [(2, true), (0, true)]) (tg .zx [2] [(1, true), (0, true)]) true,
    .swp 5 0 (tg .zx [0] [(2, true), (1, true)]) (tg .zx [1] [(2, true), (0, true)]) true,
    .sem 18 2 [] 0,
    .sem 17 2 [] 2,
    .sem 13 2 [] 0,
    .sem 12 2 [] 2,
    .sem 8 2 [] 0,
    .sem 7 2 [] 2,
    .swp 9 0 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [1] [(4, true), (3, true), (0, true)]) true,
    .swp 10 1 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) true,
    .swp 11 0 (tg .box [1] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) true,
    .sem 12 1 [tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1] 0,
    .sem 8 1 [tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0, tK 0] 3,
    .swp 7 0 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [1] [(4, true), (3, true), (0, true)]) true,
    .swp 8 1 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) true,
    .swp 9 0 (tg .box [1] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) true,
    .sem 10 1 [tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1] 0,
    .sem 6 1 [tK 0, tS 0, tC 1, tS 0, tK 0, tS 0, tC 1, tS 0] 3,
    .rw 4 2 false,
    .sw 2,
    .sem 3 1 [tp 1 [L.Z 0] [2]] 0,
    .rw 3 3 false,
    .sem 4 1 [tZ 2] 0,
    .sw 4,
    .rw 3 2 true,
    .sem 5 8 [tg .zx [0] [(2, true), (1, true)]] 3,
    .sem 9 30 [tg .box [1] [(4, true), (3, true), (2, true)]] 0,
    .swp 8 0 (tg .box [1] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) false,
    .swp 7 1 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) false,
    .swp 6 0 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [1] [(4, true), (3, true), (0, true)]) false,
    .sem 7 8 [tg .xz [0] [(2, true), (1, true)]] 3,
    .sem 11 30 [tg .box [1] [(4, true), (3, true), (2, true)]] 0,
    .swp 10 0 (tg .box [1] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) false,
    .swp 9 1 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) false,
    .swp 8 0 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [1] [(4, true), (3, true), (0, true)]) false,
    .sem 6 0 [tS 0, tS 0] 2,
    .sem 7 0 [tS 1, tS 1] 0,
    .sem 11 0 [tS 0, tS 0] 2,
    .sem 12 0 [tS 1, tS 1] 0,
    .sem 16 0 [tS 0, tS 0] 2,
    .sem 17 0 [tS 1, tS 1] 0,
    .swp 4 0 (tg .zx [0] [(2, true), (1, true)]) (tg .zx [1] [(2, true), (0, true)]) false,
    .swp 3 1 (tg .zx [1] [(2, true), (0, true)]) (tg .zx [2] [(1, true), (0, true)]) false,
    .swp 5 0 (tg .box [1] [(4, true), (3, true), (0, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) false,
    .swp 4 1 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) false,
    .swp 6 0 (tg .xz [0] [(2, true), (1, true)]) (tg .xz [1] [(2, true), (0, true)]) false,
    .swp 5 1 (tg .xz [1] [(2, true), (0, true)]) (tg .xz [2] [(1, true), (0, true)]) false,
    .swp 7 0 (tg .box [1] [(4, true), (3, true), (0, true)]) (tg .box [0] [(4, true), (3, true), (1, true)]) false,
    .swp 6 1 (tg .box [0] [(4, true), (3, true), (1, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) false,
    .sem 4 0 [tS 0, tS 0] 2,
    .sem 7 0 [tS 0, tS 0] 2,
    .sem 10 0 [tS 0, tS 0] 2,
    .rw 2 1 false,
    .swp 3 0 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [1] [(4, true), (3, true), (2, true)]) false,
    .rw 4 0 false,
    .swp 5 0 (tg .box [0] [(4, true), (3, true), (2, true)]) (tg .box [1] [(4, true), (3, true), (2, true)]) false,
    .sem 2 1 [tg .zx [2] [(1, true), (0, true)]] 3,
    .sem 4 1 [tg .xz [2] [(1, true), (0, true)]] 3,
    .sem 5 3 [tZ 2] 0,
    .sem 1 2 [] 3,
    .sem 2 3 [tC 0, tZ 2] 3,
    .sem 0 2 [tg .box [1] [(4, true), (3, true), (2, true)], tZ 2] 0,
    .sem 1 3 [tC 0] 3] = true := by
  decide +kernel

theorem t249Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L249Base0) (wcT 5 R249Base0) :=
  check_sound ih (AllD.cons (swq_entry (havail ih) 0 (by decide +kernel)) (AllD.cons (swq_entry (havail ih) 0 (by decide +kernel)) (AllD.cons (Net.der_of_eq (by set_option maxRecDepth 100000 in rfl)) (AllD.cons (rel_entry (havail ih) [0, 1] (by decide +kernel) (rule19)) (AllD.nil 5))))) run249Base0

def L250Base0 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [1] [(4, true), (3, true), (2, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def R250Base0 : List Tk := [tg .box [1] [(4, true), (3, true), (2, true)]]

def T250Base0 : Tbl := []

theorem run250Base0 : check 4 T250Base0 L250Base0 R250Base0
    [.sem 1 1 [tg .zx [1] [(3, true), (2, true)], tp 2 [L.K 0] [1, 4], tg .xz [1] [(3, true), (2, true)], tp 2 [L.K 0] [1, 4]] 0,
    .sem 0 2 [tg .xz [1] [(3, true), (2, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 4,
    .sem 1 2 [tp 2 [L.C 0] [1, 4], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 2 2 [tg .zx [1] [(3, true), (2, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 4,
    .sem 3 2 [tp 2 [L.C 0] [1, 4], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 4 2 [] 2,
    .sem 0 3 [tg .zx [1] [(3, true), (2, true)], tp 2 [L.C 0] [1, 4], tg .xz [1] [(3, true), (2, true)]] 0,
    .sem 0 4 [tg .box [1] [(4, true), (3, true), (2, true)]] 0] = true := by
  decide +kernel

theorem t250Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L250Base0) (wcT 5 R250Base0) :=
  check_sound ih (AllD.nil 5) run250Base0

def L251Base0 : List Tk := [tg .box [1] [(4, true), (3, true), (2, true)]]

def R251Base0 : List Tk := [tg .box [0] [(4, true), (3, true), (2, true)]]

def T251Base0 : Tbl := [([tC 0, tg .box [1] [(4, true), (3, true), (2, true)]], [tg .box [1] [(4, true), (3, true), (2, true)], tC 0])]

theorem run251Base0 : check 4 T251Base0 L251Base0 R251Base0
    [.sem 0 0 [tS 0, tS 0] 2,
    .sem 1 1 [tC 0, tH 0, tH 1, tC 0, tH 0, tH 1, tC 0, tH 0, tH 1] 2,
    .sem 9 2 [tg .box [1] [(4, true), (3, true), (2, true)], tH 1] 0,
    .sem 8 1 [tp 1 [L.H 0] [0]] 1,
    .sem 8 1 [tH 0] 1,
    .sem 9 1 [tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1] 0,
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
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 21,
    .sw 22,
    .sw 23,
    .sw 24,
    .sw 25,
    .sw 26,
    .sw 27,
    .sw 28,
    .sw 29,
    .sw 30,
    .sw 31,
    .sw 32,
    .sw 33,
    .sw 34,
    .sw 35,
    .sw 36,
    .sw 37,
    .sem 38 1 [tp 1 [L.H 0] [0]] 1,
    .sem 8 30 [tg .box [1] [(4, true), (3, true), (2, true)]] 0,
    .sem 9 1 [tH 0] 1,
    .rw 7 0 false,
    .sem 6 2 [tg .box [1] [(4, true), (3, true), (2, true)], tH 1] 0,
    .sem 5 1 [tp 1 [L.H 0] [0]] 1,
    .sem 5 1 [tH 0] 1,
    .sem 6 1 [tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1] 0,
    .sw 5,
    .sw 6,
    .sw 7,
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
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 21,
    .sw 22,
    .sw 23,
    .sw 24,
    .sw 25,
    .sw 26,
    .sw 27,
    .sw 28,
    .sw 29,
    .sw 30,
    .sw 31,
    .sw 32,
    .sw 33,
    .sw 34,
    .sem 35 1 [tp 1 [L.H 0] [0]] 1,
    .sem 5 30 [tg .box [1] [(4, true), (3, true), (2, true)]] 0,
    .sem 6 1 [tH 0] 1,
    .rw 4 0 false,
    .sem 3 2 [tg .box [1] [(4, true), (3, true), (2, true)], tH 1] 0,
    .sem 2 1 [tp 1 [L.H 0] [0]] 1,
    .sem 2 1 [tH 0] 1,
    .sem 3 1 [tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1, tS 1, tC 2, tS 1, tK 1, tS 1, tC 2, tS 1, tK 1, tS 1, tS 2, tS 1, tC 3, tS 1, tS 2, tS 1] 0,
    .sw 2,
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
    .sw 13,
    .sw 14,
    .sw 15,
    .sw 16,
    .sw 17,
    .sw 18,
    .sw 19,
    .sw 20,
    .sw 21,
    .sw 22,
    .sw 23,
    .sw 24,
    .sw 25,
    .sw 26,
    .sw 27,
    .sw 28,
    .sw 29,
    .sw 30,
    .sw 31,
    .sem 32 1 [tp 1 [L.H 0] [0]] 1,
    .sem 2 30 [tg .box [1] [(4, true), (3, true), (2, true)]] 0,
    .sem 3 1 [tH 0] 1,
    .rw 1 0 false,
    .sem 2 9 [tS 0] 2,
    .swp 0 0 (tg .box [1] [(4, true), (3, true), (2, true)]) (tg .box [0] [(4, true), (3, true), (2, true)]) false] = true := by
  decide +kernel

theorem t251Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L251Base0) (wcT 5 R251Base0) :=
  check_sound ih (AllD.cons (t249Base0 ih) (AllD.nil 5)) run251Base0

def L252Base0 : List Tk := [tg .hg [1, 2] [(4, true), (3, true)]]

def R252Base0 : List Tk := [tg .hg [0, 2] [(4, true), (3, true)]]

def T252Base0 : Tbl := [([tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [1] [(4, true), (3, true), (2, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]], [tg .box [1] [(4, true), (3, true), (2, true)]]),
  ([tg .box [1] [(4, true), (3, true), (2, true)]], [tg .box [0] [(4, true), (3, true), (2, true)]])]

theorem run252Base0 : check 4 T252Base0 L252Base0 R252Base0
    [.sem 0 1 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2], tg .box [1] [(4, true), (3, true), (2, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [1, 2]] 0,
    .rw 1 0 true,
    .sem 0 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 3,
    .sem 2 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 2]] 3,
    .rw 1 1 false,
    .sem 0 3 [tg .hg [0, 2] [(4, true), (3, true)]] 1] = true := by
  decide +kernel

theorem t252Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L252Base0) (wcT 5 R252Base0) :=
  check_sound ih (AllD.cons (t250Base0 ih) (AllD.cons (t251Base0 ih) (AllD.nil 5))) run252Base0

def L253Base0 : List Tk := [tg .hg [3, 1] [(2, true), (0, true)], tg .box [1] [(4, true), (2, false), (0, true)]]

def R253Base0 : List Tk := [tg .box [1] [(4, true), (2, false), (0, true)], tg .hg [3, 1] [(2, true), (0, true)]]

def T253Base0 : Tbl := [([tg .hg [4, 1] [(2, true), (0, true)]], [tg .hg [3, 1] [(2, true), (0, true)]])]

theorem run253Base0 : check 4 T253Base0 L253Base0 R253Base0
    [.rw 0 0 true,
    .sem 0 2 [tg .box [1] [(4, true), (2, false), (0, true)], tg .hg [4, 1] [(2, true), (0, true)]] 3,
    .rw 1 0 false] = true := by
  decide +kernel

theorem t253Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L253Base0) (wcT 5 R253Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 1, 0, 3, 2] (by decide +kernel) (t252Base0 ih)) (AllD.nil 5)) run253Base0

def L254Base0 : List Tk := [tg .hg [3, 1] [(2, true), (0, true)], tg .box [0] [(4, true), (2, false), (1, true)]]

def R254Base0 : List Tk := [tg .box [0] [(4, true), (2, false), (1, true)], tg .hg [3, 1] [(2, true), (0, true)]]

def T254Base0 : Tbl := [([tg .hg [4, 1] [(2, true), (0, true)]], [tg .hg [3, 1] [(2, true), (0, true)]])]

theorem run254Base0 : check 4 T254Base0 L254Base0 R254Base0
    [.rw 0 0 true,
    .sem 0 2 [tg .box [0] [(4, true), (2, false), (1, true)], tg .hg [4, 1] [(2, true), (0, true)]] 3,
    .rw 1 0 false] = true := by
  decide +kernel

theorem t254Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L254Base0) (wcT 5 R254Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 1, 0, 3, 2] (by decide +kernel) (t252Base0 ih)) (AllD.nil 5)) run254Base0

def L251Base0f2 : List Tk := [tg .box [1] [(4, true), (3, true), (2, false)]]

def R251Base0f2 : List Tk := [tg .box [0] [(4, true), (3, true), (2, false)]]

def T251Base0f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(4, true), (3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(4, true), (3, true), (2, false)]]),
  ([tg .box [1] [(4, true), (3, true), (2, true)]], [tg .box [0] [(4, true), (3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(4, true), (3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(4, true), (3, true), (2, false)]])]

theorem run251Base0f2 : check 4 T251Base0f2 L251Base0f2 R251Base0f2
    [.rw 0 0 true,
    .rw 1 1 false,
    .rw 0 2 false] = true := by
  decide +kernel

theorem t251Base0f2 (ih : IH 5) : Derivable (theory 5) (wcT 5 L251Base0f2) (wcT 5 R251Base0f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(4, true), (3, true), (2, true)] [(4, true), (3, true), (2, false)] (by decide +kernel)) (AllD.cons (t251Base0 ih) (AllD.cons (x81_entry 2 .box [0] [(4, true), (3, true), (2, true)] [(4, true), (3, true), (2, false)] (by decide +kernel)) (AllD.nil 5)))) run251Base0f2

def L255Base0 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [1] [(4, true), (2, false), (0, true)]]

def R255Base0 : List Tk := [tg .box [1] [(4, true), (2, false), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def T255Base0 : Tbl := [([tg .hg [4, 0] [(3, true), (2, true)]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tg .box [3] [(4, true), (0, true), (2, false)]], [tg .box [1] [(4, true), (0, true), (2, false)]])]

theorem run255Base0 : check 4 T255Base0 L255Base0 R255Base0
    [.rw 0 0 true,
    .sem 1 1 [tg .box [1] [(4, true), (0, true), (2, false)]] 3,
    .rw 1 1 true,
    .sem 1 1 [tg .box [3] [(4, true), (2, false), (0, true)]] 1,
    .sem 0 2 [tg .box [3] [(4, true), (2, false), (0, true)], tg .hg [4, 0] [(3, true), (2, true)]] 1,
    .sem 0 1 [tg .box [3] [(4, true), (0, true), (2, false)]] 1,
    .rw 0 1 false,
    .sem 0 1 [tg .box [1] [(4, true), (2, false), (0, true)]] 3,
    .rw 1 0 false] = true := by
  decide +kernel

theorem t255Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L255Base0) (wcT 5 R255Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 3] (by decide +kernel) (t252Base0 ih)) (AllD.cons (rel_entry (havail ih) [1, 2, 1, 0] (by decide +kernel) (t251Base0f2 ih)) (AllD.nil 5))) run255Base0

def L256Base0 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(4, true), (2, false), (1, true)]]

def R256Base0 : List Tk := [tg .box [0] [(4, true), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def T256Base0 : Tbl := [([tg .hg [4, 0] [(3, true), (2, true)]], [tg .hg [1, 0] [(3, true), (2, true)]])]

theorem run256Base0 : check 4 T256Base0 L256Base0 R256Base0
    [.sem 1 1 [tg .zx [0] [(4, true), (2, false)], tK 0, tg .xz [0] [(4, true), (2, false)], tK 0] 3,
    .rw 0 0 true,
    .sem 0 2 [tg .zx [0] [(4, true), (2, false)], tg .hg [4, 0] [(3, true), (2, true)]] 1,
    .rw 1 0 false,
    .sem 1 2 [tK 0, tg .hg [1, 0] [(3, true), (2, true)]] 4,
    .rw 2 0 true,
    .sem 2 2 [tg .xz [0] [(4, true), (2, false)], tg .hg [4, 0] [(3, true), (2, true)]] 1,
    .rw 3 0 false,
    .sem 3 2 [tK 0, tg .hg [1, 0] [(3, true), (2, true)]] 4,
    .sem 0 4 [tg .box [0] [(4, true), (2, false), (1, true)]] 3] = true := by
  decide +kernel

theorem t256Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L256Base0) (wcT 5 R256Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 3] (by decide +kernel) (t252Base0 ih)) (AllD.nil 5)) run256Base0

def L252Base0f3 : List Tk := [tg .hg [1, 2] [(4, true), (3, false)]]

def R252Base0f3 : List Tk := [tg .hg [0, 2] [(4, true), (3, false)]]

def T252Base0f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 2] [(4, true), (3, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 2] [(4, true), (3, false)]]),
  ([tg .hg [1, 2] [(4, true), (3, true)]], [tg .hg [0, 2] [(4, true), (3, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 2] [(4, true), (3, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 2] [(4, true), (3, false)]])]

theorem run252Base0f3 : check 4 T252Base0f3 L252Base0f3 R252Base0f3
    [.rw 0 0 true,
    .rw 1 1 false,
    .rw 0 2 false] = true := by
  decide +kernel

theorem t252Base0f3 (ih : IH 5) : Derivable (theory 5) (wcT 5 L252Base0f3) (wcT 5 R252Base0f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 2] [(4, true), (3, true)] [(4, true), (3, false)] (by decide +kernel)) (AllD.cons (t252Base0 ih) (AllD.cons (x81_entry 3 .hg [0, 2] [(4, true), (3, true)] [(4, true), (3, false)] (by decide +kernel)) (AllD.nil 5)))) run252Base0f3

def L257Base0 : List Tk := [tg .hg [3, 1] [(2, true), (0, true)], tg .hg [4, 1] [(2, false), (0, true)]]

def R257Base0 : List Tk := [tg .hg [4, 1] [(2, false), (0, true)], tg .hg [3, 1] [(2, true), (0, true)]]

def T257Base0 : Tbl := [([tg .hg [4, 1] [(0, true), (2, false)]], [tg .hg [3, 1] [(0, true), (2, false)]])]

theorem run257Base0 : check 4 T257Base0 L257Base0 R257Base0
    [.sem 1 1 [tg .hg [4, 1] [(0, true), (2, false)]] 3,
    .rw 1 0 false,
    .sem 1 1 [tg .hg [3, 1] [(2, false), (0, true)]] 4,
    .sem 0 2 [tg .hg [3, 1] [(2, false), (0, true)], tg .hg [3, 1] [(2, true), (0, true)]] 4,
    .sem 0 1 [tg .hg [3, 1] [(0, true), (2, false)]] 4,
    .rw 0 0 true,
    .sem 0 1 [tg .hg [4, 1] [(2, false), (0, true)]] 3] = true := by
  decide +kernel

theorem t257Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L257Base0) (wcT 5 R257Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 1, 3, 2, 1, 0] (by decide +kernel) (t252Base0f3 ih)) (AllD.nil 5)) run257Base0

def L258Base0 : List Tk := [tg .hg [3, 1] [(2, true), (0, true)], tg .hg [4, 0] [(2, false), (1, true)]]

def R258Base0 : List Tk := [tg .hg [4, 0] [(2, false), (1, true)], tg .hg [3, 1] [(2, true), (0, true)]]

def T258Base0 : Tbl := [([tg .hg [4, 0] [(1, true), (2, false)]], [tg .hg [3, 0] [(1, true), (2, false)]])]

theorem run258Base0 : check 4 T258Base0 L258Base0 R258Base0
    [.sem 1 1 [tg .hg [4, 0] [(1, true), (2, false)]] 3,
    .rw 1 0 false,
    .sem 1 1 [tg .hg [3, 0] [(2, false), (1, true)]] 4,
    .sem 0 2 [tg .hg [3, 0] [(2, false), (1, true)], tg .hg [3, 1] [(2, true), (0, true)]] 4,
    .sem 0 1 [tg .hg [3, 0] [(1, true), (2, false)]] 4,
    .rw 0 0 true,
    .sem 0 1 [tg .hg [4, 0] [(2, false), (1, true)]] 3] = true := by
  decide +kernel

theorem t258Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L258Base0) (wcT 5 R258Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 1, 3, 2, 1] (by decide +kernel) (t252Base0f3 ih)) (AllD.nil 5)) run258Base0

def L259Base0 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .hg [4, 1] [(2, false), (0, true)]]

def R259Base0 : List Tk := [tg .hg [4, 1] [(2, false), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def T259Base0 : Tbl := [([tg .hg [4, 1] [(0, true), (2, false)]], [tg .hg [3, 1] [(0, true), (2, false)]])]

theorem run259Base0 : check 4 T259Base0 L259Base0 R259Base0
    [.sem 1 1 [tg .hg [4, 1] [(0, true), (2, false)]] 3,
    .rw 1 0 false,
    .sem 1 1 [tg .hg [3, 1] [(2, false), (0, true)]] 4,
    .sem 0 2 [tg .hg [3, 1] [(2, false), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]] 4,
    .sem 0 1 [tg .hg [3, 1] [(0, true), (2, false)]] 4,
    .rw 0 0 true,
    .sem 0 1 [tg .hg [4, 1] [(2, false), (0, true)]] 3] = true := by
  decide +kernel

theorem t259Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L259Base0) (wcT 5 R259Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 1, 3, 2, 1, 0] (by decide +kernel) (t252Base0f3 ih)) (AllD.nil 5)) run259Base0

def L260Base0 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .hg [4, 0] [(2, false), (1, true)]]

def R260Base0 : List Tk := [tg .hg [4, 0] [(2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def T260Base0 : Tbl := [([tg .hg [4, 0] [(1, true), (2, false)]], [tg .hg [3, 0] [(1, true), (2, false)]])]

theorem run260Base0 : check 4 T260Base0 L260Base0 R260Base0
    [.sem 1 1 [tg .hg [4, 0] [(1, true), (2, false)]] 3,
    .rw 1 0 false,
    .sem 1 1 [tg .hg [3, 0] [(2, false), (1, true)]] 4,
    .sem 0 2 [tg .hg [3, 0] [(2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]] 4,
    .sem 0 1 [tg .hg [3, 0] [(1, true), (2, false)]] 4,
    .rw 0 0 true,
    .sem 0 1 [tg .hg [4, 0] [(2, false), (1, true)]] 3] = true := by
  decide +kernel

theorem t260Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L260Base0) (wcT 5 R260Base0) :=
  check_sound ih (AllD.cons (rel_entry (havail ih) [1, 0, 2, 1, 3, 2, 1] (by decide +kernel) (t252Base0f3 ih)) (AllD.nil 5)) run260Base0

def L267Base0 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [1] [(4, true), (2, false), (0, true)]]

def R267Base0 : List Tk := [tg .zx [1] [(4, true), (2, false), (0, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def T267Base0 : Tbl := [([tg .hg [1, 0] [(3, true), (2, true)], tg .hg [4, 1] [(2, false), (0, true)]], [tg .hg [4, 1] [(2, false), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(4, true), (2, false), (1, true)]], [tg .box [0] [(4, true), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tg .hg [3, 1] [(2, true), (0, true)], tg .hg [4, 1] [(2, false), (0, true)]], [tg .hg [4, 1] [(2, false), (0, true)], tg .hg [3, 1] [(2, true), (0, true)]]),
  ([tg .hg [3, 1] [(2, true), (0, true)], tg .box [0] [(4, true), (2, false), (1, true)]], [tg .box [0] [(4, true), (2, false), (1, true)], tg .hg [3, 1] [(2, true), (0, true)]])]

theorem run267Base0 : check 4 T267Base0 L267Base0 R267Base0
    [.sem 1 1 [tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)], tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]] 4,
    .sem 6 1 [tg .hg [4, 1] [(2, false), (0, true)], tg .box [0] [(4, true), (2, false), (1, true)], tg .hg [4, 1] [(2, false), (0, true)], tg .box [0] [(4, true), (2, false), (1, true)]] 3,
    .sem 0 6 [tg .hg [3, 1] [(2, true), (0, true)], tg .hg [1, 0] [(3, true), (2, true)], tg .hg [3, 1] [(2, true), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]] 4,
    .rw 3 0 false,
    .rw 4 1 false,
    .rw 5 0 false,
    .rw 6 1 false,
    .rw 2 2 false,
    .rw 3 3 false,
    .rw 4 2 false,
    .rw 5 3 false,
    .rw 1 0 false,
    .rw 2 1 false,
    .rw 3 0 false,
    .rw 4 1 false,
    .rw 0 2 false,
    .rw 1 3 false,
    .rw 2 2 false,
    .rw 3 3 false,
    .sem 4 4 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)], tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 4,
    .sem 0 4 [tg .zx [1] [(4, true), (2, false), (0, true)]] 3,
    .sem 2 4 [tg .zx [0] [(3, true), (2, true), (1, true)]] 4] = true := by
  decide +kernel

theorem t267Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L267Base0) (wcT 5 R267Base0) :=
  check_sound ih (AllD.cons (t259Base0 ih) (AllD.cons (t256Base0 ih) (AllD.cons (t257Base0 ih) (AllD.cons (t254Base0 ih) (AllD.nil 5))))) run267Base0

def L267Base1 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, false)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .xz [1] [(4, true), (2, false), (0, true)]]

def R267Base1 : List Tk := [tg .xz [1] [(4, true), (2, false), (0, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, false)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def T267Base1 : Tbl := [([tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [1] [(4, true), (2, false), (0, true)]], [tg .zx [1] [(4, true), (2, false), (0, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]])]

theorem run267Base1 : check 4 T267Base1 L267Base1 R267Base1
    [.sem 1 1 [tH 1, tZ 1, tH 1, tg .zx [0] [(3, true), (2, true), (1, true)], tH 1, tZ 1, tH 1] 4,
    .sem 0 9 [tZ 1, tH 1, tZ 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tZ 1, tH 1, tZ 1] 4,
    .sem 6 4 [tg .zx [1] [(4, true), (2, false), (0, true)], tZ 1, tH 1, tZ 1] 3,
    .rw 3 0 false,
    .sem 0 4 [tg .xz [1] [(4, true), (2, false), (0, true)], tZ 1, tH 1, tZ 1] 3,
    .sem 1 9 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tH 1, tZ 1, tH 1, tg .zx [0] [(3, true), (2, true), (1, true)], tH 1, tZ 1, tH 1, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 4,
    .sem 2 7 [tg .zx [0] [(3, true), (2, true), (1, false)]] 4] = true := by
  decide +kernel

theorem t267Base1 (ih : IH 5) : Derivable (theory 5) (wcT 5 L267Base1) (wcT 5 R267Base1) :=
  check_sound ih (AllD.cons (t267Base0 ih) (AllD.nil 5)) run267Base1

def L267Base0i : List Tk := [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tg .xz [0] [(3, true), (2, true), (1, true)], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tg .xz [1] [(4, true), (2, false), (0, true)]]

def R267Base0i : List Tk := [tg .xz [1] [(4, true), (2, false), (0, true)], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tg .xz [0] [(3, true), (2, true), (1, true)], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]]

def T267Base0i : Tbl := [([tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [1] [(4, true), (2, false), (0, true)]], [tg .zx [1] [(4, true), (2, false), (0, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]])]

theorem run267Base0i : check 4 T267Base0i L267Base0i R267Base0i
    [.sem 4 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 5 0 [tg .zx [0] [(3, true), (2, true), (1, true)], tg .xz [0] [(3, true), (2, true), (1, true)]] 4,
    .sem 6 0 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 7 0 [tg .zx [1] [(4, true), (2, false), (0, true)], tg .xz [1] [(4, true), (2, false), (0, true)]] 3,
    .rw 4 0 false,
    .sem 3 2 [] 3,
    .sem 2 2 [] 2,
    .sem 1 2 [] 4,
    .sem 0 2 [] 2] = true := by
  decide +kernel

theorem t267Base0i (ih : IH 5) : Derivable (theory 5) (wcT 5 L267Base0i) (wcT 5 R267Base0i) :=
  check_sound ih (AllD.cons (t267Base0 ih) (AllD.nil 5)) run267Base0i

def L267Base2 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .xz [1] [(4, true), (2, false), (0, false)]]

def R267Base2 : List Tk := [tg .xz [1] [(4, true), (2, false), (0, false)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def T267Base2 : Tbl := [([tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tg .xz [0] [(3, true), (2, true), (1, true)], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tg .xz [1] [(4, true), (2, false), (0, true)]], [tg .xz [1] [(4, true), (2, false), (0, true)], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1], tg .xz [0] [(3, true), (2, true), (1, true)], tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]])]

theorem run267Base2 : check 4 T267Base2 L267Base2 R267Base2
    [.sem 3 1 [tH 0, tZ 0, tH 0, tg .xz [1] [(4, true), (2, false), (0, true)], tH 0, tZ 0, tH 0] 3,
    .sem 2 4 [tZ 0, tH 0, tZ 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 1 4 [tZ 0, tH 0, tZ 0, tg .xz [0] [(3, true), (2, true), (1, true)]] 4,
    .sem 0 4 [tH 0, tZ 0, tH 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 3 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .sem 5 1 [tp 2 [L.S 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0, L.Z 0, L.H 1, L.K 0] [0, 1]] 2,
    .rw 3 0 false,
    .sem 4 3 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .xz [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 4,
    .sem 6 4 [tZ 0, tH 0, tZ 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 5 4 [tZ 0, tH 0, tZ 0, tg .zx [0] [(3, true), (2, true), (1, true)]] 4,
    .sem 4 4 [tH 0, tZ 0, tH 0, tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .sem 0 7 [tg .xz [1] [(4, true), (2, false), (0, false)]] 3] = true := by
  decide +kernel

theorem t267Base2 (ih : IH 5) : Derivable (theory 5) (wcT 5 L267Base2) (wcT 5 R267Base2) :=
  check_sound ih (AllD.cons (t267Base0i ih) (AllD.nil 5)) run267Base2

def L268Base0 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(4, true), (2, false), (1, true)]]

def R268Base0 : List Tk := [tg .zx [0] [(4, true), (2, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .zx [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def T268Base0 : Tbl := [([tg .hg [1, 0] [(3, true), (2, true)], tg .hg [4, 0] [(2, false), (1, true)]], [tg .hg [4, 0] [(2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tg .hg [1, 0] [(3, true), (2, true)], tg .box [1] [(4, true), (2, false), (0, true)]], [tg .box [1] [(4, true), (2, false), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tg .hg [3, 1] [(2, true), (0, true)], tg .hg [4, 0] [(2, false), (1, true)]], [tg .hg [4, 0] [(2, false), (1, true)], tg .hg [3, 1] [(2, true), (0, true)]]),
  ([tg .hg [3, 1] [(2, true), (0, true)], tg .box [1] [(4, true), (2, false), (0, true)]], [tg .box [1] [(4, true), (2, false), (0, true)], tg .hg [3, 1] [(2, true), (0, true)]])]

theorem run268Base0 : check 4 T268Base0 L268Base0 R268Base0
    [.sem 1 1 [tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)], tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)]] 4,
    .sem 6 1 [tg .hg [4, 0] [(2, false), (1, true)], tg .box [1] [(4, true), (2, false), (0, true)], tg .hg [4, 0] [(2, false), (1, true)], tg .box [1] [(4, true), (2, false), (0, true)]] 3,
    .sem 0 6 [tg .hg [3, 1] [(2, true), (0, true)], tg .hg [1, 0] [(3, true), (2, true)], tg .hg [3, 1] [(2, true), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]] 4,
    .rw 3 0 false,
    .rw 4 1 false,
    .rw 5 0 false,
    .rw 6 1 false,
    .rw 2 2 false,
    .rw 3 3 false,
    .rw 4 2 false,
    .rw 5 3 false,
    .rw 1 0 false,
    .rw 2 1 false,
    .rw 3 0 false,
    .rw 4 1 false,
    .rw 0 2 false,
    .rw 1 3 false,
    .rw 2 2 false,
    .rw 3 3 false,
    .sem 4 4 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)], tg .hg [3, 0] [(2, true), (1, true)], tg .box [1] [(3, true), (2, true), (0, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 4,
    .sem 0 4 [tg .zx [0] [(4, true), (2, false), (1, true)]] 3,
    .sem 2 4 [tg .zx [0] [(3, true), (2, true), (1, true)]] 4] = true := by
  decide +kernel

theorem t268Base0 (ih : IH 5) : Derivable (theory 5) (wcT 5 L268Base0) (wcT 5 R268Base0) :=
  check_sound ih (AllD.cons (t260Base0 ih) (AllD.cons (t255Base0 ih) (AllD.cons (t258Base0 ih) (AllD.cons (t253Base0 ih) (AllD.nil 5))))) run268Base0

end QCert.RealCliffordCH.Sec8.D.W5T
