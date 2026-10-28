/-
Copyright (c) 2026 QCert contributors. All rights reserved.

The conjugated local rotations of (322), (323) commute with a box whose
control on wire 2 has the opposite colour. Expanding the box on wire 4
leaves four-wire rotations handled by (267), (268), and an inner box.
The inner box is idle on wire 4, so its commutation follows directly from
the smaller-width completeness hypothesis.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E322a

namespace QCert.RealCliffordCH.Sec8.D.N13
open Circuit Eng SE Net N8

def W322 (one a α β : Bool) : List Lt := if one then W1 a α β else W0 a α β
def B322 (γ : Bool) : Lt := .g .box [0] [(1, γ), (2, false), (4, true)] true
def I322 (γ : Bool) : Lt := .g .box [0] [(1, γ), (2, false)] true
def P322 (γ : Bool) : List Lt :=
  [Qa true γ, Qb γ true, I322 γ, Qb (!γ) true, Qa false γ,
    Qb γ true, I322 γ, Qb (!γ) true]

theorem chk_exp322 : ∀ γ : Bool,
    check 4 [] [B322 γ] (P322 γ) [.sem 0 1 (P322 γ) 3] = true := by
  decide +kernel

theorem chk_inner322 : ∀ one a α β γ : Bool,
    check 4 [] (W322 one a α β ++ [I322 γ]) ([I322 γ] ++ W322 one a α β)
      [.sem 0 22 ([I322 γ] ++ W322 one a α β) 4] = true := by
  decide +kernel

def T322 (one a α β γ : Bool) : SE.Tbl :=
  [([B322 γ], P322 γ),
   (W322 one a α β ++ [Qa true γ], [Qa true γ] ++ W322 one a α β),
   (W322 one a α β ++ [Qb γ true], [Qb γ true] ++ W322 one a α β),
   (W322 one a α β ++ [I322 γ], [I322 γ] ++ W322 one a α β),
   (W322 one a α β ++ [Qb (!γ) true], [Qb (!γ) true] ++ W322 one a α β),
   (W322 one a α β ++ [Qa false γ], [Qa false γ] ++ W322 one a α β)]

theorem T322_ok (m : ℕ) (ih : IH (m + 5)) (one a α β γ : Bool) :
    AllD 5 m (T322 one a α β γ) := by
  intro e he
  simp only [T322, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact check_sound (frame 4) ih (allD_nil 5 m) (chk_exp322 γ)
  · cases one
    · exact e268 m ih a α true β γ
    · exact e267s m ih a α true β γ
  · cases one
    · exact e267 m ih a α γ β true
    · exact e268s m ih a α γ β true
  · exact check_sound (frame 4) ih (allD_nil 5 m) (chk_inner322 one a α β γ)
  · cases one
    · exact e267 m ih a α (!γ) β true
    · exact e268s m ih a α (!γ) β true
  · cases one
    · exact e268 m ih a α false β γ
    · exact e267s m ih a α false β γ

def run322 : List St :=
  [.rw 21 0 false, .rw 0 1 false, .rw 1 2 false, .rw 2 3 false,
   .rw 3 4 false, .rw 4 5 false, .rw 5 2 false, .rw 6 3 false,
   .rw 7 4 false, .rw 0 0 true]

theorem chk322 : ∀ one a α β γ : Bool,
    check 4 (T322 one a α β γ) (W322 one a α β ++ [B322 γ])
      ([B322 γ] ++ W322 one a α β) run322 = true := by
  decide +kernel

theorem r322 (m : ℕ) (ih : IH (m + 5)) (one a α β γ : Bool) :
    Derivable (theory (m + 5)) (wc 5 (m + 5) (W322 one a α β ++ [B322 γ]))
      (wc 5 (m + 5) ([B322 γ] ++ W322 one a α β)) :=
  check_sound (frame 4) ih (T322_ok m ih one a α β γ) (chk322 one a α β γ)

end QCert.RealCliffordCH.Sec8.D.N13
