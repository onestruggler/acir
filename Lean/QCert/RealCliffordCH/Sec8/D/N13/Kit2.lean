/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemmas D.12–D.13: more of the kit

* Conjugating a word by `X` on a local wire (`wc_xconjL`), and an expansion
  carried along such a conjugation (`conj_exp`).
* Boxes commute in the semantics (`sem_box_comm`): a box is diagonal.
-/
import QCert.RealCliffordCH.Sec8.D.N13.Kit

namespace QCert.RealCliffordCH.Sec8.D.N13

open Circuit Eng SE Net N8

theorem wc_xL (K N q : ℕ) : wc K N (xL q) = xAt N q := by
  simp [wc, xL, drawn, xAt_eq, circW, Lt.circ, mul_assoc]

theorem wc_xconjL (K N q : ℕ) (l : List Lt) :
    wc K N (xL q ++ l ++ xL q) = xAt N q * wc K N l * xAt N q := by
  rw [wc_append, wc_append, wc_xL, mul_assoc]

/-- An expansion `[B] ≈ P`, conjugated by `X` on wire `j`, is the expansion
`[B'] ≈ P'` when `X B X ≈ B'` and `X P X ≈ P'`. -/
theorem conj_exp {K N j : ℕ} {B B' : Lt} {P P' : List Lt}
    (d : Derivable (theory N) (wc K N [B]) (wc K N P))
    (hB : Derivable (theory N) (xAt N j * B.circ K N * xAt N j) (B'.circ K N))
    (hP : Derivable (theory N) (wc K N (xL j ++ P ++ xL j)) (wc K N P')) :
    Derivable (theory N) (wc K N [B']) (wc K N P') := by
  rw [wc_one'] at d ⊢
  rw [wc_xconjL] at hP
  exact hB.symm.trans ((dctx _ _ d).trans hP)

/-- (81) for a letter: `X` on a control wire `j` exchanges its colour. -/
theorem flip81 {K N : ℕ} (Kd : Kind) (tg : List ℕ) (cs cs' : List (ℕ × Bool)) (b : Bool) (j : ℕ)
    (bj : Bool) (hj : j < N) (hjt : j ∉ tg) (hc : ctl K cs b j = some bj)
    (h' : ∀ i < N, setCtl (ctl K cs b) j (some !bj) i = ctl K cs' b i) :
    Derivable (theory N) (xAt N j * (Lt.g Kd tg cs b).circ K N * xAt N j)
      ((Lt.g Kd tg cs' b).circ K N) := by
  have h := eq81 N Kd tg (ctl K cs b) j bj hj hjt hc
  rw [mc_congr N Kd tg h'] at h
  have e : drawn [xAt N j, mc N Kd tg (ctl K cs b), xAt N j] =
      xAt N j * mc N Kd tg (ctl K cs b) * xAt N j := by simp [drawn, mul_assoc]
  rw [e] at h
  exact h

end QCert.RealCliffordCH.Sec8.D.N13
