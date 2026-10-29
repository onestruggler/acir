/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): renaming a Figure 8 equation by a Hadamard-free word

A Hadamard-free word `P` with an inverse `P'` conjugates each letter
`H_[a,b]H_[c,d]` whose signs agree along both pairs into the letter on the
images of the indices (`hh_conj`), and each `(-1)_[a](-1)_[c]` likewise
(`conj_zz`).  So it conjugates a whole word of such letters (`conj_list`),
and any equation of Figure 8 between such words holds at the renamed indices
(`ren_eq`).  This is how Equations (45) and (46), stated at the first eight
indices, are used at other indices.
-/
import QCert.RealCliffordCH.Sec8.A.ItemBCon

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- A letter `H_[a,b]H_[c,d]` or `(-1)_[a](-1)_[c]` with natural-number indices. -/
inductive CL
  | hh (a b c d : ℕ)
  | zz (a c : ℕ)

/-- The letter of `𝒫_{2ⁿ}`. -/
def CL.toPG (n : ℕ) : CL → PG (2 ^ n)
  | .hh a b c d => Hh n a b c d
  | .zz a c => Zz n a c

/-- The letter on renamed indices. -/
def CL.ren (ρ : ℕ → ℕ) : CL → CL
  | .hh a b c d => .hh (ρ a) (ρ b) (ρ c) (ρ d)
  | .zz a c => .zz (ρ a) (ρ c)

/-- What conjugation by `P` needs of a letter. -/
def CL.Ok (n : ℕ) (P : List NL) : CL → Prop
  | .hh a b c d => a < 2 ^ n ∧ b < 2 ^ n ∧ c < 2 ^ n ∧ d < 2 ^ n ∧ Distinct4 a b c d ∧
      negL P a = negL P b ∧ negL P c = negL P d
  | .zz a c => a < 2 ^ n ∧ c < 2 ^ n

section Conj

variable (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {P P' : List NL} (hbd : ∀ y ∈ P, y.Bd n)
  (hbd' : ∀ y ∈ P', y.Bd n) (hpr : ∀ y ∈ P, y.Pr) (hpr' : ∀ y ∈ P', y.Pr)
  (hinv : ∀ v < 2 ^ n, permL (P ++ P') v = v ∧ negL (P ++ P') v = false)
include h8 hE hbd hbd' hpr hpr' hinv

theorem conj_one {x : CL} (hx : x.Ok n P) :
    D8 n (P.map (NL.toPG n) ++ x.toPG n :: P'.map (NL.toPG n)) [(x.ren (permL P)).toPG n] := by
  cases x with
  | hh a b c d =>
    obtain ⟨ha, hb, hc, hd, h, s1, s2⟩ := hx
    exact hh_conj h8 hE hbd hbd' hpr hpr' hinv ha hb hc hd h s1 s2
  | zz a c =>
    obtain ⟨ha, hc⟩ := hx
    have k := conj_zz hbd hbd' hinv ha hc
    have e1 : P.map (NL.toPG n) ++ (CL.zz a c).toPG n :: P'.map (NL.toPG n) =
        (P ++ [NL.zz a c] ++ P').map (NL.toPG n) := by simp [NL.toPG, CL.toPG]
    rw [e1]
    have hall : ∀ y ∈ P ++ [NL.zz a c] ++ P', y.Bd n ∧ y.Pr := by
      intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with (hy | rfl) | hy
      · exact ⟨hbd y hy, hpr y hy⟩
      · exact ⟨⟨ha, hc⟩, trivial⟩
      · exact ⟨hbd' y hy, hpr' y hy⟩
    exact A5s (by omega) (HP_NL (fun y hy => (hall y hy).1) (fun y hy => (hall y hy).2))
      (HP_zz _ _) k

/-- Conjugating a word of such letters. -/
theorem conj_list : ∀ L : List CL, (∀ x ∈ L, x.Ok n P) →
    D8 n (P.map (NL.toPG n) ++ L.map (CL.toPG n) ++ P'.map (NL.toPG n))
      ((L.map (CL.ren (permL P))).map (CL.toPG n))
  | [], _ => by simpa using (cancel_NL (by omega) hbd hbd' hpr hpr' hinv).1
  | x :: L, hL => by
    have c2 := (cancel_NL (by omega) hbd hbd' hpr hpr' hinv).2
    have ih := conj_list L (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    have h1 := conj_one h8 hE hbd hbd' hpr hpr' hinv (hL x (by simp))
    have ins := DR.ctx (P.map (NL.toPG n) ++ [x.toPG n])
      (L.map (CL.toPG n) ++ P'.map (NL.toPG n)) c2.symm
    refine (DR.rfl' (by simp)).trans (ins.trans ((DR.rfl' (by simp)).trans
      ((DR.append h1 ih).trans (DR.rfl' (by simp)))))

/-- An equation between words of such letters, renamed by `P`. -/
theorem ren_eq {L R : List CL} (hL : ∀ x ∈ L, x.Ok n P) (hR : ∀ x ∈ R, x.Ok n P)
    (h : D8 n (L.map (CL.toPG n)) (R.map (CL.toPG n))) :
    D8 n ((L.map (CL.ren (permL P))).map (CL.toPG n))
      ((R.map (CL.ren (permL P))).map (CL.toPG n)) :=
  (conj_list h8 hE hbd hbd' hpr hpr' hinv L hL).symm.trans
    ((DR.ctx _ _ h).trans (conj_list h8 hE hbd hbd' hpr hpr' hinv R hR))

end Conj

end QCert.RealCliffordCH.Sec8
